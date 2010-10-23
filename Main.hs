{-# LANGUAGE CPP, StandaloneDeriving, DeriveDataTypeable #-}
import System.IO
import System.Process
import System.Directory
import System.FilePath
import System.Time

import Control.Monad.Trans
import Control.Monad.State
import Control.Monad.Error

import Agda.Syntax.Concrete hiding (Name)
import Agda.Syntax.Common
import qualified Agda.Syntax.Abstract as A
import Agda.TypeChecking.Monad hiding (MetaInfo, Constructor, setCommandLineOptions)
import Agda.Interaction.Imports hiding (getInterface', createInterface)
import Agda.Interaction.Options
import Agda.Interaction.Highlighting.Range
import Agda.Interaction.Highlighting.Precise
import Agda.Interaction.Options
import Agda.Interaction.FindFile
import Agda.Utils.Monad hiding ((<.>))
import Agda.Utils.FileName
import Agda.Utils.Pretty hiding (text)
import qualified Agda.Utils.IO.Locale as LocIO
import Agda.Syntax.Parser
import Agda.Interaction.GhciTop hiding (Range, Name)
import Agda.Termination.TermCheck


import Control.Applicative
import Control.Monad
import Data.Function
import Data.Monoid
import Data.Maybe
import qualified Data.Map as Map
import qualified Data.Set as Set
import Prelude hiding (span, div)
import Data.List hiding (span)
import Data.Either

import Text.Blaze
import Text.Blaze.Html5 hiding (map, source)
import Text.Blaze.Html5.Attributes hiding (span, id)
import Text.Blaze.Renderer.String

import Text.Pandoc.Parsing
import Text.Pandoc.Shared
import Text.Pandoc.Readers.Markdown
import Text.Pandoc.Writers.HTML

import Data.Foldable (foldMap)

import SyntaxInfo

#define __IMPOSSIBLE__ (error "impossible")

toLit :: String -> String
toLit = unlines . concat . map wrap . groupBy ((==) `on` ("> " `isPrefixOf`)) . lines
  where wrap xs@(('>':' ':_):_) = (["\\begin{code}"] ++) . (++ ["\\end{code}"]) . map (drop 2) $ xs
        wrap xs = xs

withTempFile :: MonadIO m => String -> (FilePath -> Handle -> m a) -> m a
withTempFile n f = 
  do tempFolder <- liftIO $ return "/Users/pumpkin/tmp" -- getTemporaryDirectory
     let path = tempFolder </> n
     h <- liftIO $ openBinaryFile path WriteMode
     res <- f path h
     liftIO $ hClose h
     liftIO $ removeFile path
     return res

type AnnotatedCode = [(String, Maybe MetaInfo)]

correlate :: String -> CompressedFile -> AnnotatedCode
correlate = correlate' 1
  where
  correlate' i [] [] = []
  correlate' i s [] = [(s, Nothing)]
  correlate' i s ((Range f t, m):xs) = if i == f
                                         then let (x, y) = splitAt (fromIntegral (t - i)) s in (x, Just m) : correlate' t y xs
                                         else let (x, y') = splitAt (fromIntegral (f - i)) s 
                                                  (y, z) = splitAt (fromIntegral (t - f)) y' in (x, Nothing) : (y, Just m) : correlate' t z xs

isLeft :: Either a b -> Bool
isLeft (Left _) = True
isLeft _ = False

-- Assumes the list is homogeneous (kind of like a two-way sequence) and non-empty
flattenH :: [Either a b] -> Either [a] [b]
flattenH [] = error "who knows"
flattenH xs@(Left  _ : _) = Left (lefts xs)
flattenH xs@(Right _ : _) = Right (rights xs)

separate :: [(String, Maybe MetaInfo)] -> [Either String AnnotatedCode]
separate = map (either (Left . concat) Right . flattenH) . groupBy ((==) `on` isLeft) . separate' False
  where
  separate' _ [] = []
  separate' False ((str, info):xs) = if "\\begin{code}" `isInfixOf` str then separate' True xs else Left str : separate' False xs
  separate' True  ((str, info):xs) = if "\\end{code}" `isInfixOf` str then separate' False xs else Right (str, info) : separate' True xs

toHtml :: AnnotatedCode -> Html
toHtml = mconcat . map (uncurry annotate)
  where 
  annotate :: String -> Maybe MetaInfo -> Html
  annotate s Nothing = string s
  annotate s (Just i) = case aspect i of
                          Nothing -> span $ string s
                          Just i -> span ! class_ (stringValue . concat . intersperse " " $ aspectClasses i) $ string s

  aspectClasses (Name mKind op) = kindClass ++ opClass
    where
    kindClass = maybe [] (pure . showKind) mKind

    showKind (Constructor Inductive)   = "InductiveConstructor"
    showKind (Constructor CoInductive) = "CoinductiveConstructor"
    showKind k                         = show k

    opClass = if op then ["Operator"] else []
  aspectClasses a = [show a]

highlight :: [Either String AnnotatedCode] -> [Either String Html]
highlight = map (either Left (Right . toHtml))

processLiterate' :: String -> String -> TCM [Either String Html]
processLiterate' src name = do
  let lit = toLit src
  (i, w) <- withTempFile (name <.> "lagda") $ \path h -> do
    liftIO $ hSetEncoding h utf8
    liftIO $ hPutStr h lit
    liftIO $ hFlush h
    liftIO $ hClose h
    setCommandLineOptions $ (either (error "wtf") id $ parseStandardOptions ["-v0"]) { optIncludeDirs = Right [mkAbsolute (takeDirectory path), mkAbsolute "/Users/pumpkin/.agda/lib/src"] }
    typeCheck' (mkAbsolute path)
  
  return . map (either Left (Right . toHtml)) . separate . correlate lit . iHighlighting $ i
  
processLiterate :: String -> String -> IO [Either String Html]
processLiterate src name = fmap (either (error "Failed!") id) . runTCM $ processLiterate' src name



-- Shudder
wrapHtml :: String -> String
wrapHtml s = "<html><head><meta http-equiv=\"Content-Type\" content=\"text/html; charset=UTF-8\"/><link href=\"Agda.css\" rel=\"stylesheet\" type=\"text/css\"/></head><body>" ++ s ++ "</body></html>"

toSimpleHtml :: String -> String -> IO String
toSimpleHtml src name = do
  literate <- processLiterate src name
  return . wrapHtml $ concatMap (either (writeHtmlString defaultWriterOptions . readMarkdown defaultParserState) (renderHtml . (pre ! class_ (stringValue "code")))) literate
  

  
typeCheck' :: AbsolutePath -> TCM (Interface, Maybe Warnings)
typeCheck' f = do
  m <- moduleName {- where -} f 

  (i, wt) <- getInterface' m True
  return (i, case wt of
    Left w  -> Just w
    Right _ -> Nothing)

getInterface' :: TopLevelModuleName
              -> Bool  -- ^ If type checking is necessary, should all
                       -- state changes inflicted by 'createInterface'
                       -- be preserved?
              -> TCM (Interface, Either Warnings ClockTime)
getInterface' x includeStateChanges =
  -- Preserve the pragma options unless includeStateChanges is True.
  bracket (stPragmaOptions <$> get)
          (unless includeStateChanges . setPragmaOptions) $ \_ -> do
   -- Forget the pragma options (locally).
   setCommandLineOptions . stPersistentOptions =<< get

   alreadyVisited x $ addImportCycleCheck x $ do
    file <- findFile x  -- requires source to exist

    reportSLn "import.iface" 10 $ "  Check for cycle"
    checkForImportCycle

    uptodate <- ifM ignoreInterfaces
		    (return False)
		    (liftIO $ filePath (toIFile file)
                                `isNewerThan`
                              filePath file)

    reportSLn "import.iface" 5 $
      "  " ++ render (pretty x) ++ " is " ++
      (if uptodate then "" else "not ") ++ "up-to-date."

    (stateChangesIncluded, (i, wt)) <- typeCheck file

    -- Ensure that the given module name matches the one in the file.
    let topLevelName = A.toTopLevelModuleName $ iModuleName i
    unless (topLevelName == x) $ do
      checkModuleName topLevelName file
      typeError $ OverlappingProjects file topLevelName x

    visited <- isVisited x
    reportSLn "import.iface" 5 $ if visited then "  We've been here. Don't merge."
                                 else "  New module. Let's check it out."
    unless (visited || stateChangesIncluded) $ mergeInterface i

    modify (\s -> s { stCurrentModule = Just $ iModuleName i })

    -- Interfaces are only stored if no warnings were encountered.
    case wt of
      Left  w -> return ()
      Right t -> storeDecodedModule i t

    return (i, wt)

    where
	typeCheck file = do
	    -- Do the type checking.
            reportSLn "" 1 $ "Checking " ++ render (pretty x) ++ " (" ++ filePath file ++ ")."
            if includeStateChanges then do
              r <- createInterface file x

              -- Merge the signature with the signature for imported
              -- things.
              sig <- getSignature
              addImportedThings sig Map.empty Set.empty
              setSignature emptySignature

              return (True, r)
             else do
              ms       <- getImportPath
              mf       <- stModuleToSource <$> get
              vs       <- getVisitedModules
              ds       <- getDecodedModules
              opts     <- stPersistentOptions <$> get
              isig     <- getImportedSignature
              ibuiltin <- gets stImportedBuiltins
              -- Every interface is treated in isolation.
              r <- liftIO $ runTCM $
                     withImportPath ms $ do
                       setDecodedModules ds
                       setCommandLineOptions opts
                       modify $ \s -> s { stModuleToSource = mf }
                       setVisitedModules vs
                       addImportedThings isig ibuiltin Set.empty

                       r <- createInterface file x

                       mf        <- stModuleToSource <$> get
                       vs        <- getVisitedModules
                       ds        <- getDecodedModules
                       isig      <- getImportedSignature
                       ibuiltin  <- gets stImportedBuiltins
                       hsImports <- getHaskellImports
                       return (r, do
                         modify $ \s -> s { stModuleToSource = mf }
                         setVisitedModules vs
                         setDecodedModules ds

                         addImportedThings isig ibuiltin hsImports)

              case r of
                  Left err               -> throwError err
                  Right (result, update) -> do
                    update
                    return (False, result)

createInterface
  :: AbsolutePath          -- ^ The file to type check.
  -> TopLevelModuleName    -- ^ The expected module name.
  -> TCM (Interface, Either Warnings ClockTime)
createInterface file mname = do
    reportSLn "import.iface.create" 5  $
      "Creating interface for " ++ render (pretty mname) ++ "."
    verboseS "import.iface.create" 10 $ do
      visited <- Map.keys <$> getVisitedModules
      liftIO $ LocIO.putStrLn $
        "  visited: " ++ intercalate ", " (map (render . pretty) visited)

    previousHsImports <- getHaskellImports

    (pragmas, top) <- liftIO $ parseFile' moduleParser {- where -} file

    pragmas <- concat <$> concreteToAbstract_ pragmas
               -- identity for top-level pragmas at the moment
    let getOptions (A.OptionsPragma opts) = Just opts
        getOptions _                      = Nothing
        options = catMaybes $ map getOptions pragmas
    mapM_ setOptionsFromPragma options
    topLevel <- concreteToAbstract_ (TopLevel top)

    termErrs <- catchError (do
      -- Type checking.
      checkDecls (topLevelDecls topLevel)

      -- Termination checking.
      termErrs <- ifM (optTerminationCheck <$> pragmaOptions)
                      (termDecls $ topLevelDecls topLevel)
                      (return [])
      mapM_ (\e -> reportSLn "term.warn.no" 2
                     (show (fst e) ++
                      " does NOT pass the termination checker."))
            termErrs
      return termErrs
      ) (\e -> do
        -- If there is an error syntax highlighting info can still be
        -- generated.
        case rStart $ getRange e of
          Just (Pn { srcFile = Just f }) | f == file -> do
            syntaxInfo <- generateSyntaxInfo file (Just e) topLevel []
            modFile    <- stModuleToSource <$> get
            -- The highlighting info is included with the error.
            case errHighlighting e of
              Just _  -> __IMPOSSIBLE__
              Nothing ->
                throwError $ e { errHighlighting =
                                   Just (syntaxInfo, modFile) }
          _ -> throwError e
      )

    -- Generate syntax highlighting info.
    syntaxInfo <- generateSyntaxInfo file Nothing topLevel termErrs

    -- Check if there are unsolved meta-variables...
    unsolvedOK    <- optAllowUnsolved <$> pragmaOptions
    unsolvedMetas <- nub <$> (mapM getMetaRange =<< getOpenMetas)
    unless (null unsolvedMetas || unsolvedOK) $
      typeError $ UnsolvedMetas unsolvedMetas

    -- ...or unsolved constraints
    unsolvedConstraints <- getConstraints
    unless (null unsolvedConstraints || unsolvedOK) $
      typeError $ UnsolvedConstraints unsolvedConstraints

    setScope $ outsideScope topLevel

    reportSLn "scope.top" 50 $ "SCOPE " ++ show (insideScope topLevel)

    i <- buildInterface topLevel syntaxInfo previousHsImports options

    if and [ null termErrs, null unsolvedMetas, null unsolvedConstraints ]
     then do
      -- The file was successfully type-checked (and no warnings were
      -- encountered), so the interface should be written out.
      t <- writeInterface (filePath $ toIFile file) i
      return (i, Right t)
     else
      return (i, Left $ Warnings termErrs unsolvedMetas unsolvedConstraints)

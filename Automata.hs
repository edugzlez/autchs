module Automata(Automata, Status (..), AFD (..), AFN (..), AFNe (..), isRenewed, normalizeNodes, afneToafn, afnToafd, reduce, toFile, fromFile) where

------------------------------------------
-- Tipo de dato para manejar estados  
-- La idea es manejar estados simples
-- Q 0, Q 1..., así como estados producto
------------------------------------------

data Status = Void | Q Int | QT [Status]
    deriving (Show, Ord, Read)

instance Eq Status where
    (==) Void Void = True
    (==) (Q m) (Q n) = m == n 
    (==) (QT xs) (QT ys) = quicksort(removeDuplicates xs) == quicksort(removeDuplicates ys)
    (==) _ _ = False
    
------------------------------------------
-- Repertorio de funciones auxiliares  
------------------------------------------

{-
    sort :: ls1 -> ls2 -> ls

    Ordena la lista
-}

quicksort :: (Ord a) => [a] -> [a]
quicksort [] = []
quicksort (x:xs) =
  let ls = quicksort [a | a <- xs, a <= x]
      rs = quicksort [a | a <- xs, a > x]
  in ls ++ [x] ++ rs

{-
    removeDuplicates lst

    Elimina duplicados de la lista
-}

removeDuplicates :: (Eq a) => [a] -> [a]
removeDuplicates = foldl (\seen x -> if x `elem` seen then seen else seen ++ [x]) []

{-
    hasIntersect :: ls1 -> ls2 -> Bool

    Decide si dos listas se intercan 
-}

hasIntersect :: Eq a => [a] -> [a] -> Bool
hasIntersect xs ys = any (`elem` ys) xs

{-
    powerSet :: ls -> powLs

    Dada una lista ls devuelve la lista formada por las sublistas de las mismas. 
-}

powerset :: [a] -> [[a]]
powerset [] = [[]]
powerset (x:xs) = [x:ps | ps <- powerset xs] ++ powerset xs


{-
    indexOf
-}

indexOf :: Eq a => a -> [a] -> Int
indexOf e xs = indexOf' e xs 0

indexOf' :: Eq a => a -> [a] -> Int -> Int
indexOf' _ [] _ = -1
indexOf' e (x:xs) n
    | x == e = n
    | otherwise = indexOf' e xs (n+1)

------------------------------------------
-- Definición de autómatas       
------------------------------------------

{-
    Clase Automata
-}

class Automata a where
    {-
        isRenewed :: automata -> word -> isRenewed?

        Devuelve si una cadena de caracteres word es reconocida por el autómata.
    -}

    isRenewed :: a -> [Char] -> Bool

    {-
        deltaA :: automata -> word -> q0 -> qs

        Dado un autómata, una cadena de caracteres y un estado inicial, dice hasta qué conjunto de estados
        llega al final de la palabra.
    -}

    deltaA :: a -> [Char] -> Status -> [Status]

    {-
        deltaB :: automata -> word -> qi -> qs

        Dado un autómata, una cadena de caracteres y un conjunto de estados iniciales, dice hasta qué 
        conjunto de estados llega al final de la palabra.
    -}

    deltaB :: a -> [Char] -> [Status] -> [Status]


{-
    Autómata finito determinista
    
    vocab nodes initial delta terminals
-}

data AFD = AFD [Char] [Status] Status (Char -> Status -> Status) [Status]

instance Automata AFD where
    
    deltaA _ [] q0 = [q0]
    deltaA afd (x:word) q0 = deltaA afd word (delta x q0)
        where
            (AFD _ _ _ delta _) = afd
    
    
    
    deltaB _ [] qs = qs
    deltaB _ _ [] = []
    deltaB (AFD vocab nodes initial delta terminals) (x:word) qs = deltaB (AFD vocab nodes initial delta terminals) word nqs 
        where
            nqs = [q | q <- map (delta x) qs, q /= Void]

    
    
    isRenewed afd word = final_q `elem` terminals
        where
            (AFD _ _ initial _ terminals) = afd
            [final_q] = deltaB afd word [initial]

instance Show AFD where
    show (AFD vocab nodes initial delta terminals) = unlines [vocab, show nodes, show initial, show [(q,a,delta a q)| q <-nodes,a <- vocab],show terminals]

instance Read AFD where
    readsPrec _ txt = [(AFD vocab nodes initial delta terminals, "")]
        where 
            lin = lines txt
            vocab = head lin
            nodes = read (lin !! 1)::[Status]
            initial = read (lin !! 2)::Status
            deltas = read (lin !! 3)::[(Status, Char, Status)]
            delta :: Char -> Status -> Status
            delta a q
                | length lst == 1 = let (_, _, z) = head lst in z
                | otherwise = Void
                where
                    lst = filter (\(x,y,_) -> x == q && a == y) deltas
            terminals = read (lin !! 4)::[Status]
    
{-
    normalizeNodes :: automata -> automata_normalizado

    Dado un autómata lo convierte a uno con los estados al tipo Q n.
-}

normalizeNodes :: AFD -> AFD
normalizeNodes (AFD vocab nodes initial delta terminals) = AFD vocab nodes' initial' delta' terminals'
    where
        nodes' = map Q [0..(length nodes-1)]
        initial' = Q (indexOf initial nodes)
        delta' :: Char -> Status -> Status
        delta' c (Q n)
            | (n < length nodes) && (n>= 0) && (c `elem` vocab) = Q (indexOf (delta c (nodes !! n)) nodes)
            | otherwise = Void

        delta' _ _ = Void

        terminals' = filter (\(Q n) -> (nodes !! n) `elem` terminals) nodes'

{-
   reduce :: automata -> automata_reducido

   Dado un autómata elimina sus nodos inalcanzables
-}

reduce :: AFD -> AFD
reduce (AFD vocab nodes initial delta terminals) = AFD vocab nodes' initial delta' terminals'
 where
        nodes' = alcanzables (AFD vocab nodes initial delta terminals)
        delta' :: Char -> Status -> Status
        delta' c a
          | a `elem` nodes' = delta c a
          | otherwise = Void
        terminals' = [a | a <- nodes', a `elem` terminals]

{-
   alcanzables :: automata -> lista_alcanzables

   Dado un autómata devuelve una lista con los estados alcanzables desde el inicial. alcanzables' es una función auxiliar.
-}

alcanzables :: AFD -> [Status]
alcanzables (AFD vocab nodes initial delta terminals) = alcanzables' (AFD vocab nodes initial delta terminals) [] [initial]

alcanzables' :: AFD -> [Status] -> [Status] -> [Status]
alcanzables' _ xs [] = xs
alcanzables' at xs (q:ys)
   | q `elem` xs = alcanzables' at xs ys
   | otherwise = alcanzables' at (q:xs) (ys++[delta a q | a <- vocab])
   where
       (AFD vocab _ _ delta _) = at

{-
    Autómata finito no determinista

    vocab nodes initial delta terminals
-}


data AFN = AFN [Char] [Status] Status (Char -> Status -> [Status]) [Status]

instance Automata AFN where
    
    deltaA _ [] q0 = [q0]
    deltaA afn word q0 = deltaB afn word [q0]
    
    deltaB _ [] qs = qs
    deltaB _ _ [] = []
    deltaB (AFN vocab nodes initial delta terminals) (x:word) qs = deltaB (AFN vocab nodes initial delta terminals) word nqs 
        where
            nqs = concatMap (delta x) qs

    isRenewed afn word = hasIntersect final_qs terminals
        where
            (AFN _ _ initial _ terminals) = afn
            final_qs = deltaA afn word initial

instance Show AFN where
    show (AFN vocab nodes initial delta terminals) = unlines [vocab, show nodes, show initial, show [(q,a,delta a q)| q <-nodes,a <- vocab],show terminals]

{-
    afnToafd :: AFN -> AFD

    convierte AFN a AFD
-}

afnToafd :: AFN -> AFD
afnToafd (AFN vocab nodes initial delta terminals) = AFD vocab' nodes' initial' delta' terminals'
    where
        afn = AFN vocab nodes initial delta terminals
        vocab' = vocab
        nodes' = map QT (powerset nodes)

        initial' = QT [initial]

        delta' :: Char -> Status -> Status
        delta' c (QT qs) = QT (deltaB afn [c] qs)
        delta' _ _ = Void

        terminals' = [QT qs | (QT qs) <- nodes', hasIntersect qs terminals]

{-
    Autómata finito no determinista con transiciones libres

    vocab nodes initial delta terminals epsilon
-}

data AFNe = AFNe [Char] [Status] Status (Char -> Status -> [Status]) [Status] (Status -> [Status])

instance Automata AFNe where
    
    deltaA _ [] q0 = [q0]
    deltaA afn word q0 = deltaB afn word [q0]
    
    deltaB _ [] qs = qs
    deltaB _ _ [] = []
    deltaB (AFNe vocab nodes initial delta terminals epsilon) (x:word) qs = deltaB (AFNe vocab nodes initial delta terminals epsilon) word nqs_cierre 
        where
            qs_cierre =  concatMap (closureEps (AFNe vocab nodes initial delta terminals epsilon)) qs
            nqs = concatMap (delta x) qs_cierre
            nqs_cierre = concatMap (closureEps (AFNe vocab nodes initial delta terminals epsilon)) nqs

    isRenewed afn word = hasIntersect final_qs terminals
        where
            (AFNe _ _ initial _ terminals _) = afn
            final_qs = deltaA afn word initial

instance Show AFNe where
    show (AFNe vocab nodes initial delta terminals epsilon) = unlines [vocab, show nodes, show initial, show [(q,a,delta a q)| q <-nodes,a <- vocab], show terminals, show [(q,epsilon q)| q <-nodes]]

{-
    reachableEps :: automata -> status

    automata : Autómata de donde se obtiene la función delta.
    status : estado

    -> devuelve una lista de estados que son los que se alcanzan con el cierre epsilon, sin contar el estado de entrada status.
-}

reachableEps :: AFNe -> Status -> [Status]
reachableEps (AFNe vocab nodes initial delta terminals epsilon) q = foldr (++) primerCierre reachable
    where
        reachable = map (reachableEps (AFNe vocab nodes initial delta terminals epsilon)) primerCierre
        primerCierre = epsilon q

{-
    closureEps :: automata -> status

    automata : Autómata de donde se obtiene la función delta.
    status : estado

    -> devuelve una lista de estados que son los que se alcanzan con el cierre epsilon.
-}

closureEps :: AFNe -> Status -> [Status]
closureEps at q = q : reachableEps at q

{-
    afneToafn :: AFNe -> AFN

    convierte AFNe a AFN
-}

afneToafn :: AFNe -> AFN
afneToafn (AFNe vocab nodes initial delta terminals epsilon) = AFN vocab' nodes' initial' delta' terminals'
    where
        afne = AFNe vocab nodes initial delta terminals epsilon
        vocab' = vocab
        nodes' = nodes

        initial' = initial

        delta' :: Char -> Status -> [Status]
        delta' c q = qs
            where
                qcierre =  closureEps afne q
                qs = concatMap (delta c) qcierre
        
        terminals' = [q | q <- nodes', hasIntersect (closureEps afne q) terminals]

{-    
    toFile :: object -> filename ->

    Imprime el objeto object, instancia de Show, en el archivo filename
-}

toFile :: Automata a => Show a => a -> [Char] -> IO ()
toFile at c = do writeFile c (show at)

{-    
    EN CUARENTENA
-}

fromFile :: [Char] -> IO AFD
fromFile filepath = do
    file <- readFile filepath
    let at = read file::AFD in return at
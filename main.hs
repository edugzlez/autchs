import Automata

delta :: Char -> Status -> [Status]
delta 'a' (Q 0) = [Q 1]
delta 'a' (Q 1) = [Q 1]
delta 'b' (Q 1) = [Q 1]
delta 'a' (Q 2) = [Q 2]
delta 'b' (Q 2) = [Q 2, Q 3]
delta _ _ = []


epsilon :: Status -> [Status]
epsilon (Q 100) = [Q 0, Q 2]
epsilon _ = []

a = AFNe "ab" [Q 100, Q 0, Q 1, Q 2, Q 3] (Q 100) delta [Q 1, Q 3] epsilon
b = normalizeNodes (afnToafd (afneToafn a))
(AFD vocab' nodes' initial' delta' terminals') = b
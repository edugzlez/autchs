import Automata

-- Expresiones regulares 'a' y 'b'
a = RexChar 'a'
b = RexChar 'b'

-- Suma OR
cualquiera = 'a' |+| 'b'

-- Cierre *
todapalabra = (|^|) cualquiera

-- Concatenación *
terminaEnA = todapalabra |++| a

-- AFNe correspondiente
afn = regToAFNe terminaEnA
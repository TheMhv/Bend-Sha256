type Bits:
  e
  o {~pred: Bits}
  i {~pred: Bits}

# Show
Bits.show: Bits -> String
Bits.show Bits/e = (String/Nil)
Bits.show (Bits/o pred) = (String/Cons '0' (Bits.show pred))
Bits.show (Bits/i pred) = (String/Cons '1' (Bits.show pred))

# Lenght
Bits.len: Bits -> u24
Bits.len Bits/e = (0)
Bits.len (Bits/i pred) = (+ 1 (Bits.len pred))
Bits.len (Bits/o pred) = (+ 1 (Bits.len pred))

# Bitwise NOT
Bits.not: Bits -> Bits
Bits.not Bits/e = (Bits/e)
Bits.not (Bits/o pred) = (Bits/i (Bits.not pred))
Bits.not (Bits/i pred) = (Bits/o (Bits.not pred))

# Bitwise AND
Bits.and: Bits -> Bits -> Bits
Bits.and (Bits/o x.pred) (Bits/o y.pred) = (Bits/o (Bits.and x.pred y.pred))
Bits.and (Bits/i x.pred) (Bits/o y.pred) = (Bits/o (Bits.and x.pred y.pred))
Bits.and (Bits/o x.pred) (Bits/i y.pred) = (Bits/o (Bits.and x.pred y.pred))
Bits.and (Bits/i x.pred) (Bits/i y.pred) = (Bits/i (Bits.and x.pred y.pred))
Bits.and * * = (Bits/e)

# Bitwise OR
Bits.or: Bits -> Bits -> Bits
Bits.or (Bits/o x.pred) (Bits/o y.pred) = (Bits/o (Bits.or x.pred y.pred))
Bits.or (Bits/i x.pred) (Bits/o y.pred) = (Bits/i (Bits.or x.pred y.pred))
Bits.or (Bits/o x.pred) (Bits/i y.pred) = (Bits/i (Bits.or x.pred y.pred))
Bits.or (Bits/i x.pred) (Bits/i y.pred) = (Bits/i (Bits.or x.pred y.pred))
Bits.or * * = (Bits/e)

# Bitwise XOR
Bits.xor: Bits -> Bits -> Bits
Bits.xor (Bits/o x.pred) (Bits/o y.pred) = (Bits/o (Bits.xor x.pred y.pred))
Bits.xor (Bits/i x.pred) (Bits/o y.pred) = (Bits/i (Bits.xor x.pred y.pred))
Bits.xor (Bits/o x.pred) (Bits/i y.pred) = (Bits/i (Bits.xor x.pred y.pred))
Bits.xor (Bits/i x.pred) (Bits/i y.pred) = (Bits/o (Bits.xor x.pred y.pred))
Bits.xor * * = (Bits/e)

# Concat
Bits.concat: Bits -> Bits -> Bits
Bits.concat Bits/e y = (y)
Bits.concat (Bits/o pred) y = (Bits/o (Bits.concat pred y))
Bits.concat (Bits/i pred) y = (Bits/i (Bits.concat pred y))

# Rotr
Bits.rotr: Bits -> Bits
Bits.rotr Bits/e = (Bits/e)
Bits.rotr (Bits/o pred) = (Bits.concat pred (Bits/o (Bits/e)))
Bits.rotr (Bits/i pred) = (Bits.concat pred (Bits/i (Bits/e)))

# Shift
Bits.shr: Bits -> Bits
Bits.shr Bits/e = (Bits/e)
Bits.shr (Bits/o pred) = (Bits.concat pred (Bits/o (Bits/e)))
Bits.shr (Bits/i pred) = (Bits.concat pred (Bits/o (Bits/e)))

# Incremment
Bits.incr: Bits -> Bits
Bits.incr Bits/e = (Bits/i (Bits/e))
Bits.incr (Bits/o pred) = (Bits/i (pred))
Bits.incr (Bits/i pred) = (Bits/o (Bits.incr(pred)))

# Sum
Bits.sum: Bits -> Bits -> Bits
Bits.sum Bits/e Bits/e = (Bits/e)
Bits.sum Bits/e y = (y)
Bits.sum x Bits/e = (x)
Bits.sum (Bits/o x.pred) (Bits/o y.pred) = (Bits/o (Bits.sum x.pred y.pred))
Bits.sum (Bits/i x.pred) (Bits/o y.pred) = (Bits/i (Bits.sum x.pred y.pred))
Bits.sum (Bits/o x.pred) (Bits/i y.pred) = (Bits/i (Bits.sum x.pred y.pred))
Bits.sum (Bits/i x.pred) (Bits/i y.pred) = (Bits/o (Bits.incr (Bits.sum x.pred y.pred)))

# Slice
Bits.slice: Bits -> u24 -> Bits
Bits.slice * 0 = (Bits/e)
Bits.slice Bits/e * = (Bits/e)
Bits.slice (Bits/o pred) n = (Bits/o (Bits.slice pred (- n 1)))
Bits.slice (Bits/i pred) n = (Bits/i (Bits.slice pred (- n 1)))

# Jump
Bits.jmp: Bits -> u24 -> Bits
Bits.jmp x 0 = (x)
Bits.jmp Bits/e * = (Bits/e)
Bits.jmp (Bits/o pred) n = (Bits.jmp pred (- n 1))
Bits.jmp (Bits/i pred) n = (Bits.jmp pred (- n 1))

# Split
Bits.split: Bits -> u24 -> (List Bits)
Bits.split Bits/e n = (List/Nil)
Bits.split x n = (List/Cons (Bits.slice x n) (Bits.split (Bits.jmp x n) n))

# Reverse
Bits.rev: Bits -> Bits
Bits.rev Bits/e = (Bits/e)
Bits.rev (Bits/o pred) = (Bits.concat (Bits.rev pred) (Bits/o(Bits/e)))
Bits.rev (Bits/i pred) = (Bits.concat (Bits.rev pred) (Bits/i(Bits/e)))

# Fill
Bits.fill: Bits -> u24 -> Bits
Bits.fill x 0 = (x)
Bits.fill x n = (Bits.fill (Bits.concat (Bits/o(Bits/e)) x) (- n 1))

# Padding
Bits.padding: Bits -> u24 -> Bits
Bits.padding x 0 = (x)
Bits.padding x n = (Bits.padding (Bits.concat x (Bits/o(Bits/e))) (- n 1))

# Binary String to Bits
Bits.from_string: String -> Bits
Bits.from_string String/Nil = (Bits/e)
Bits.from_string (String/Cons 49 tail) = (Bits/i(Bits.from_string tail))
Bits.from_string (String/Cons x tail) = (Bits/o(Bits.from_string tail))

# String to Bits
Bits.encode: String -> Bits
Bits.encode String/Nil = (Bits/e)
Bits.encode (String/Cons head tail) = (
  Bits.concat 
    (Bits.encode tail)
    (Bits.padding 
      (Bits.from_decimal head)
      (- 8 (Bits.len (Bits.from_decimal head)))
    )
)

# Decimal to Bits
Bits.from_decimal: u24 -> Bits
Bits.from_decimal 0 = (Bits/e)
Bits.from_decimal x = if (== (% x 2) 0) {
  (Bits/o (Bits.from_decimal (/ x 2)))
} else {
  (Bits/i (Bits.from_decimal (/ x 2)))
}

# Bits to decimal
Bits.to_decimal.loop: Bits -> u24 -> u24
Bits.to_decimal.loop Bits/e n = (0)
Bits.to_decimal.loop (Bits/o pred) n = (Bits.to_decimal.loop pred (+ n 1))
Bits.to_decimal.loop (Bits/i pred) n = (+ (^ 2 n) (Bits.to_decimal.loop pred (+ n 1)))

Bits.to_decimal: Bits -> u24
Bits.to_decimal x = (Bits.to_decimal.loop x 0)
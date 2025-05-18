from ./bits import (
  Bits,
  Bits.and,
  Bits.concat,
  Bits.encode,
  Bits.fill,
  Bits.from_decimal,
  Bits.from_string,
  Bits.len,
  Bits.not,
  Bits.padding,
  Bits.rev,
  Bits.rotr,
  Bits.show
  Bits.shr,
  Bits.slice,
  Bits.split,
  Bits.sum,
  Bits.xor
)

# Loop
loop: (T -> T) -> T -> u24 -> T
loop * arg 0 = (arg)
loop f arg n = (loop f (f arg) (- n 1))

# List.get
List.get: (List Any) -> u24 -> Any
List.get List/Nil _ = (List/Nil)
List.get (List/Cons head _) 0 = (head)
List.get (List/Cons head tail) n = (List.get tail (- n 1))

# List.set
List.set: (List T) -> T -> u24 -> (List T)
List.set List/Nil * * = (List/Nil)
List.set (List/Cons * tail) x 0 = (List/Cons x tail)
List.set (List/Cons head tail) x n = (List/Cons head (List.set tail x (- n 1)))

# Bits List Loop
Bits.List.loop: (Bits -> T) -> (List Bits) -> (List T)
Bits.List.loop _ List/Nil = (List/Nil)
Bits.List.loop f (List/Cons head tail) = (List/Cons (f head) (Bits.List.loop f tail))

Bits.List.to_bits: (List Bits) -> Bits
Bits.List.to_bits (List/Nil) = (Bits/e)
Bits.List.to_bits (List/Cons head tail) = (Bits.concat head (Bits.List.to_bits tail))

# Sha256 bits sum needs to slice as 32 bits
Sha256.Bits.sum: Bits -> Bits -> Bits
Sha256.Bits.sum x y = (Bits.slice (Bits.sum x y) 32)

# ==============

# Choice
Sha256.choice: Bits -> Bits -> Bits -> Bits
Sha256.choice x y z = (Bits.xor (Bits.and x y) (Bits.and (Bits.not(x)) z))

# Majority
Sha256.majority: Bits -> Bits -> Bits -> Bits
Sha256.majority x y z = (Bits.xor (Bits.xor (Bits.and x y) (Bits.and x z)) (Bits.and y z))

# σ0
Sha256.sigma0: Bits -> Bits
Sha256.sigma0 x = (Bits.xor (Bits.xor (loop Bits.rotr x 7) (loop Bits.rotr x 18)) (loop Bits.shr x 3))

# σ1
Sha256.sigma1: Bits -> Bits
Sha256.sigma1 x = (Bits.xor (Bits.xor (loop Bits.rotr x 17) (loop Bits.rotr x 19)) (loop Bits.shr x 10))

# Σ0
Sha256.usigma0: Bits -> Bits
Sha256.usigma0 x = (Bits.xor (Bits.xor (loop Bits.rotr x 2) (loop Bits.rotr x 13)) (loop Bits.rotr x 22))

# Σ1
Sha256.usigma1: Bits -> Bits
Sha256.usigma1 x = (Bits.xor (Bits.xor (loop Bits.rotr x 6) (loop Bits.rotr x 11)) (loop Bits.rotr x 25))

# Temp1 = Σ1(e) + Ch(e, f, g) + h + Kt + Wt
Sha256.temp1: Bits -> Bits -> Bits -> Bits -> Bits -> Bits -> Bits
Sha256.temp1 e f g h wi ki = (  
  Sha256.Bits.sum (Sha256.usigma1 e) (
    Bits.sum (Sha256.choice e f g) (
      Bits.sum h (
        Bits.sum ki wi
      )
    )
  )
)

# Temp2 = Σ0(a) + Maj(a, b, c)
Sha256.temp2: Bits -> Bits -> Bits -> Bits
Sha256.temp2 a b c = (Sha256.Bits.sum (Sha256.usigma0 a) (Sha256.majority a b c))

# Message
Sha256.message: String -> Bits
Sha256.message x = (Bits.encode x)

# Padding
Sha256.padding: Bits -> Bits
Sha256.padding message = (
  Bits.concat 
  (Bits.padding 
    (Bits.from_decimal (Bits.len message))
    (- 64 (Bits.len (Bits.from_decimal (Bits.len message))))
  )
  (Bits.fill
    (Bits.concat (Bits/i(Bits/e)) message)
    (% (+ (% (- 448 (+ (Bits.len message) 1)) 512) 512) 512)
    # (% (- 448 (+ (Bits.len message) 1)) 512)
  )
)

# Schedule
Sha256.schedule: Bits -> (List Bits)
Sha256.schedule block = (Sha256.schedule.loop (Bits.split block 32) 48)

# Schedule loop
Sha256.schedule.loop: (List Bits) -> u24 -> (List Bits)
Sha256.schedule.loop List/Nil * = (List/Nil)
Sha256.schedule.loop chunk 0 = (chunk)
Sha256.schedule.loop chunk n = (
  Sha256.schedule.loop
    (List/Cons (
      Sha256.Bits.sum (List.get chunk 15) (
        Bits.sum (List.get chunk 6) (
          Bits.sum (Sha256.sigma0 (List.get chunk 14)) (
            Sha256.sigma1 (List.get chunk 1)
          )
        )
      )
    ) chunk)
  (- n 1)
)

# Constant
Sha256.constants: (List Bits)
Sha256.constants = ([
  (Bits.from_string "00011001111101000101000101000010"),
  (Bits.from_string "10001001001000101110110010001110"),
  (Bits.from_string "11110011110111110000001110101101"),
  (Bits.from_string "10100101110110111010110110010111"),
  (Bits.from_string "11011010010000110110101010011100"),
  (Bits.from_string "10001111100010001000111110011010"),
  (Bits.from_string "00100101010000011111110001001001"),
  (Bits.from_string "10101011011110100011100011010101"),
  (Bits.from_string "00011001010101011110000000011011"),
  (Bits.from_string "10000000110110101100000101001000"),
  (Bits.from_string "01111101101000011000110000100100"),
  (Bits.from_string "11000011101111100011000010101010"),
  (Bits.from_string "00101110101110100111110101001110"),
  (Bits.from_string "01111111100011010111101100000001"),
  (Bits.from_string "11100101011000000011101111011001"),
  (Bits.from_string "00101110100011111101100110000011"),
  (Bits.from_string "10000011100101101101100100100111"),
  (Bits.from_string "01100001111000100111110111110111"),
  (Bits.from_string "01100011101110011000001111110000"),
  (Bits.from_string "00110011100001010011000000100100"),
  (Bits.from_string "11110110001101001001011110110100"),
  (Bits.from_string "01010101001000010010111001010010"),
  (Bits.from_string "00111011100101010000110100111010"),
  (Bits.from_string "01011011000100011001111101101110"),
  (Bits.from_string "01001010100010100111110000011001"),
  (Bits.from_string "10110110011000111000110000010101"),
  (Bits.from_string "00010011111001001100000000001101"),
  (Bits.from_string "11100011111111101001101011111101"),
  (Bits.from_string "11001111110100000000011101100011"),
  (Bits.from_string "11100010100010011110010110101011"),
  (Bits.from_string "10001010110001100101001101100000"),
  (Bits.from_string "11100110100101001001010000101000"),
  (Bits.from_string "10100001010100001110110111100100"),
  (Bits.from_string "00011100100001001101100001110100"),
  (Bits.from_string "00111111101101100011010010110010"),
  (Bits.from_string "11001000101100000001110011001010"),
  (Bits.from_string "00101010110011100101000010100110"),
  (Bits.from_string "11011101010100000101011001101110"),
  (Bits.from_string "01110100100100110100001110000001"),
  (Bits.from_string "10100001001101000100111001001001"),
  (Bits.from_string "10000101000101111111110101000101"),
  (Bits.from_string "11010010011001100101100000010101"),
  (Bits.from_string "00001110110100011101001001000011"),
  (Bits.from_string "11000101100010100011011011100011"),
  (Bits.from_string "10011000000101110100100110001011"),
  (Bits.from_string "00100100011000001001100101101011"),
  (Bits.from_string "10100001101011000111000000101111"),
  (Bits.from_string "00001110000001010101011000001000"),
  (Bits.from_string "01101000100000110010010110011000"),
  (Bits.from_string "00010000001101101110110001111000"),
  (Bits.from_string "00110010111011100001001011100100"),
  (Bits.from_string "10101101001111010000110100101100"),
  (Bits.from_string "11001101001100000011100010011100"),
  (Bits.from_string "01010010010101010001101101110010"),
  (Bits.from_string "11110010010100110011100111011010"),
  (Bits.from_string "11001111111101100111010000010110"),
  (Bits.from_string "01110111010000011111000100101110"),
  (Bits.from_string "11110110110001101010010100011110"),
  (Bits.from_string "00101000000111100001001100100001"),
  (Bits.from_string "00010000010000001110001100110001"),
  (Bits.from_string "01011111111111110111110100001001"),
  (Bits.from_string "11010111001101100000101000100101"),
  (Bits.from_string "11101111110001011001111101111101"),
  (Bits.from_string "01001111000111101000111001100011")
])

# Initial Hashes
Sha256.hashes: (List Bits)
Sha256.hashes = ([
  (Bits.from_string "11100110011001111001000001010110"), # A
  (Bits.from_string "10100001011101011110011011011101"), # B
  (Bits.from_string "01001110110011110111011000111100"), # C
  (Bits.from_string "01011100101011111111001010100101"), # D
  (Bits.from_string "11111110010010100111000010001010"), # E
  (Bits.from_string "00110001000101101010000011011001"), # F
  (Bits.from_string "11010101100110111100000111111000"), # G
  (Bits.from_string "10011000101100110000011111011010")  # H
])

Sha256.compression: Bits -> Bits -> Bits -> Bits -> Bits -> Bits -> Bits -> Bits -> (List Bits) -> (List Bits) -> (List Bits)
Sha256.compression a b c d e f g h List/Nil * = ([a b c d e f g h])
Sha256.compression a b c d e f g h * List/Nil = ([a b c d e f g h])
Sha256.compression a b c d e f g h (List/Cons Wi Wtail) (List/Cons Ki Ktail) = 
  let t1 = (Sha256.temp1 e f g h Wi Ki)
  (Sha256.compression (Sha256.Bits.sum t1 (Sha256.temp2 a b c)) a b c (Sha256.Bits.sum d t1) e f g Wtail Ktail)

Sha256.finalHash: (List Bits) -> (List Bits) -> (List Bits)
Sha256.finalHash List/Nil * = (List/Nil)
Sha256.finalHash * List/Nil = (List/Nil)
Sha256.finalHash (List/Cons cHead cTail) (List/Cons hHead hTail) = (List/Cons (Sha256.Bits.sum cHead hHead) (Sha256.finalHash cTail hTail))

Sha256.updateHashes: (List Bits) -> (List Bits) -> (List Bits)
Sha256.updateHashes hashes List/Nil = (hashes)
Sha256.updateHashes h (List/Cons s sTail) = (Sha256.updateHashes
  (Sha256.finalHash 
    (Sha256.compression
      (List.get h 0)
      (List.get h 1)
      (List.get h 2)
      (List.get h 3)
      (List.get h 4)
      (List.get h 5)
      (List.get h 6)
      (List.get h 7)
      (List/reverse (Sha256.schedule s))
      (Sha256.constants)
    )
    h
  )
  sTail
)

Sha256.digest: String -> Bits
Sha256.digest x = (Bits.List.to_bits (Bits.List.loop Bits.rev (Sha256.updateHashes Sha256.hashes (List/reverse (Bits.split (Sha256.padding (Bits.encode x)) 512)))))

main: String
main x = (Bits.show (Sha256.digest x))
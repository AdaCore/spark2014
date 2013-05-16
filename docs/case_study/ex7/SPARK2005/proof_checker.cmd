6.
replace h#1:A ** B by A * (A ** (B - 1)) using exp(4).
1.
yes
yes
standardise h#1.
standardise c#1.
done.

10.
prove c#1 by cases on a >= 0 or a < 0.
done.
done.

infer c * a ** b <= 2147483647 using inequals from [1,3].
infer c * a ** b >= -2147483648 using inequals from [1,2].
replace h#19:A ** B by A * (A ** (B - 1)) using exp(4).
yes
replace h#20:A ** B by A * (A ** (B - 1)) using exp(4).
yes

# prove c#2 by cases on c >= 0 or c < 0.

# infer a * a ** (b - 1) <= c * (a * a ** (b - 1)) using inequals.

7.
unwrap c#1.
prove c#1 by impl.
infer int_n__1 = 3 using WILD from [11,12].
replace all:int_n__1 by 3 using eq.
replace all:3 - 2 by 1 using eq.
replace all:2 ** 1 by 2 using eq.
replace all: element(a, [2]) by 1 using eq.
replace all: element(a, [1]) by 1 using eq.
replace all: 1 + 1 by 2 using eq.
forwardchain h#13.
simplify.
forwardchain h#17.
replace all:3 - 1 by 2 using eq.
replace c#1: fib(3) by fib(2) + fib(1) using eq.
replace c#1:fib(2) by 1 using eq.
replace c#1:fib(1) by 1 using eq.
replace c#1:1 + 1 by 2 using eq.
done.

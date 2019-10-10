package Repro is

   type Some_Type is private;

   procedure Foo (Low : in Some_Type; High : in Some_Type);

private
   type Some_Type is mod 2 ** 64;
end Repro;

package Interpol
  with SPARK_Mode
is
   pragma Elaborate_Body;

   subtype Arg is Integer range 0 .. 10_000;
   subtype Value is Integer range 0 .. 1_000;
   type Point is record
      X : Arg;
      Y : Value;
   end record;

   type Index is new Integer range 1 .. 100;

   type Func is array (Index range <>) of Point with
     Predicate => Func'First = 1
       and then (for all I in 1 .. Func'Last =>
                  (if I /= Func'Last then Func(I).X < Func(I+1).X));

   function Increasing (F : Func) return Boolean is
     (for all I in F'Range =>
        (for all J in F'Range =>
           (if I < J then F(I).Y <= F(J).Y)));

   subtype Monotonic_Incr_Func is Func with
     Predicate => Increasing (Monotonic_Incr_Func);

   type Func2 is array (Index range <>) of Point with
     Predicate => Func2'First = 1
       and then (for all I in 1 .. Func2'Last =>
                   (for all J in 1 .. Func2'Last =>
                      (if I < J then Func2(I).X < Func2(J).X)));

   function Increasing2 (F : Func2) return Boolean is
     (for all I in F'Range =>
        (for all J in F'Range =>
           (if I < J then F(I).Y <= F(J).Y)));

   subtype Monotonic_Incr_Func2 is Func2 with
     Predicate => Increasing2 (Monotonic_Incr_Func2);

end Interpol;

package P
  with SPARK_Mode => On
is

   function Add_Or_Subtract (I : Integer) return Integer
      with Pre => I in Natural,
           Post => Add_Or_Subtract'Result in Natural;

   function Assume_Natural (X : Integer) return Integer;
   --  Assumes that X is natural

   procedure Annotate_Intentional (C : Boolean);
   --  Has annotations justifying uninitialized variables

   Foo : Integer;

end P;

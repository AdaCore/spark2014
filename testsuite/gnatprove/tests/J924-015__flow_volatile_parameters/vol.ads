package Vol with
  SPARK_Mode
is

   type T is record
      C : Integer;
   end record with Volatile;

   V : T;

   procedure Assign (X : out T);

   procedure Proc with
     Global => (Output => V);

end Vol;

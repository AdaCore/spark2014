procedure Foo with SPARK_Mode is
   type R is record
      F, G : Integer;
   end record;
   type T is access R;

   procedure P (X : out T) with Import;

   procedure Call_P is
      X : T with Relaxed_Initialization;
   begin
      P (X);
   end Call_P;

begin
   null;
end Foo;

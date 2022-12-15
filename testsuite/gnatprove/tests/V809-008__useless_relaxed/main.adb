procedure Main
  with
    SPARK_Mode => On
is

   C : constant Integer := 15 with
     Relaxed_Initialization;  -- Useless

   type R is record
      F, G : Integer;
   end record with
     Predicate => F < G;

   D : constant R := (1, 2) with
     Relaxed_Initialization;  -- Useless

   type H is record
      C : R;
   end record;

   V : H with
     Relaxed_Initialization;  -- OK

   E : constant H := V with
     Relaxed_Initialization;  -- OK
begin
   null;
end Main;

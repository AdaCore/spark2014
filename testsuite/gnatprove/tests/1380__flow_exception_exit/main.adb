procedure Main with SPARK_Mode is

   type R is record
      F : Integer;
   end record;

   procedure P (B1 : Boolean; X : in out R) with
     Import,
     Always_Terminates,
     Global => null,
     Exit_Cases =>
       (B1 => (Exception_Raised => Program_Error),
        others => Normal_Return);

   procedure Call_P (B1 : Boolean; X : in out R) with
     Exit_Cases =>
       (B1 => (Exception_Raised => Program_Error),
        others => Normal_Return);

   procedure Call_P (B1 : Boolean; X : in out R) is
   begin
      P (B1, X);
   end Call_P;
begin
   null;
end Main;

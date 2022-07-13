procedure Test_Ownership_Flow with SPARK_Mode is

   package Nested is
      type T1 is private with
        Annotate => (GNATprove, Ownership, "Needs_Reclamation"); --  << OK
   private
      pragma SPARK_Mode (Off);
      type T1 is null record;
   end Nested;
   use Nested;

   G : Boolean := True;

   function F (X : T1) return Boolean is (G) with
     Annotate => (GNATprove, Ownership, "Is_Reclaimed"); --  << KO, ownership function shall not access global data
begin
   null;
end;

with Priv; use Priv;
procedure Main (Max : Natural) with SPARK_Mode is
   type R is record
      Content : Priv_Rec (Max);
   end record;

   procedure Init (X : in out R) is
   begin
      Init (X.Content); -- @PRECONDITION:FAIL
   end Init;

   V : R;
begin
   Init (V); -- This call should be inlined
end Main;

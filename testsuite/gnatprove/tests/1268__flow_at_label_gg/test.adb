pragma Extensions_Allowed (All_Extensions);

package body Test with SPARK_Mode is
   type Rec is record
      A : Integer;
      B : Integer;
   end record;

   X : Integer := 0;
   R : Rec := (A => 0, B => 0);

   procedure Main (C : Integer; O : out Integer) is
   begin
      X := C;
      R.A := C;
      <<Init>>

      declare
         Scalar_Snapshot    : constant Integer := X'At (Init);
         Component_Snapshot : constant Integer := R'At (Init).A;

         procedure Check_Scalar with
           Pre => Scalar_Snapshot = C;

         procedure Check_Component with
           Pre => Component_Snapshot = C;

         procedure Check_Scalar is null;
         procedure Check_Component is null;
      begin
         Check_Scalar;
         Check_Component;
         O := X + R.A;
      end;
   end Main;
end Test;

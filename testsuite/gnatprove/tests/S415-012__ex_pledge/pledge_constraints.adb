procedure Pledge_Constraints with SPARK_Mode is
   type Int_Acc is access Integer;
   type Int_Acc_Option (Present : Boolean := False) is record
      case Present is
      when True => Content : Int_Acc;
      when False => null;
      end case;
   end record;
   type Int_Opt_Arr is array (Positive range <>) of Int_Acc_Option;
   type Int_Arr_Acc is access Int_Opt_Arr;
   type Two_Arrays is record
      A1, A2 : Int_Arr_Acc;
   end record;

   function Pledge (T : access Integer; B : Boolean) return Boolean is (B) with Ghost;
   pragma Annotate (GNATprove, Pledge, Entity => Pledge);

   procedure Update (X : in out Two_Arrays) with
     Pre => X.A1 /= null and then 1 in X.A1'Range and then X.A1 (1).Present
     and then X.A1 (1).Content /= null
   is
      Y : access Integer := X.A1 (1).Content;
   begin
      X.A2 := new Int_Opt_Arr'(1 .. 3 => (Present => False));
      Y.all := 15;
      pragma Assert (Pledge (Y, X.A1 (1).Content.all = Y.all));
      pragma Assert (Pledge (Y, not X.A2 (1).Present)); --@ASSERT:FAIL --@DEREFERENCE_CHECK:FAIL --@INDEX_CHECK:FAIL
   end Update;
begin
   null;
end Pledge_Constraints;

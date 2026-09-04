pragma Extensions_Allowed (All_Extensions);

procedure Test
  (P_In1, P_In2, P_Proof, P_Unused : Integer; P_Out : out Boolean)
with
  SPARK_Mode,
  Pre     => P_Proof > 1 and then P_In1 > 0,
  Depends => (P_Out => (P_In1, P_In2), null => (P_Proof, P_Unused))
is
   function Fun (F_In, F_Unused : Integer) return Boolean
   with
     Global  => (Input => P_In2, Proof_In => P_Proof),
     Pre     => P_Proof > 0,
     Depends => (Fun'Result => (F_In, P_In2), null => F_Unused);

   function Fun (F_In, F_Unused : Integer) return Boolean is
   begin
      pragma Assert (P_Proof /= 0);
      return F_In = P_In2;
   end Fun;

begin
   --  Verify that normal fall-through enters the label snapshot machinery and
   --  that Inputs, Proof_Ins, and Null_Deps remain separate.

   <<Lbl>>
   P_Out := Fun (P_In1, P_Unused)'At (Lbl);
end;

package P is
   pragma Elaborate_Body;
   CAE : Boolean := True with Constant_After_Elaboration;
   function Fun return Boolean is (CAE) with Global => CAE;
end;

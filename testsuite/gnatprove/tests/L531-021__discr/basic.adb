package body Basic is

   procedure P (V : R) is
      Z : Integer;
   begin
      case V.X is
         when A =>
            if V.A_Field = 0 then
               Z := 1;
            end if;
         when B =>

            if V.A_Field = 0 then -- @DISCRIMINANT_CHECK:FAIL
               Z := 1;
            end if;
         when C =>
            if V.C_Field1 then
               Z := V.C_Field2;
            end if;
      end case;
   end P;

end Basic;

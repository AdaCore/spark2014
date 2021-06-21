with P1.Proxy;
package body P1 with Refined_State => (S1 => P1.P2.P3.S3) is
   package body P2 is
      package body P3 with Refined_State => (S3 => X3) is
         X3 : Boolean;
         procedure Me3 is
         begin
            X3 := True;
         end;
      begin
         P1.Proxy;
      end;
   end;
end;

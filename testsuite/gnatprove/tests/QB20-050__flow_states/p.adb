package body P with Refined_State => (SP => Q.SQ) is
   package body Q with Refined_State => (SQ => R.SR) is
      package body R with Refined_State => (SR => X) is
         X : Boolean := True;

         procedure Flip is
         begin
            pragma Assert (X);
         end;
      end;
   end;
end;

with Gen;
package body Gen_Actual is
   protected body PO is
      procedure Proc is
         package Instance is new Gen (X); -- X is variable here
      begin
         null;
      end;

      function Fun return Boolean is
         package Instance is new Gen (X); -- X is constant here
      begin
         return True;
      end Fun;
   end;
end;

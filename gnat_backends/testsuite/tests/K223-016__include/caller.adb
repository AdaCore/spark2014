with Callee;
package body Caller is
   procedure MyAdd(i1 : in out Integer; i2: Integer) is
   begin
      Callee.Add(i1, i2);
   end MyAdd;
end Caller;

with Callee;
package body Caller is
   procedure MyAdd(i1 : in out Integer) is
   begin
      Callee.Add(i1, 1);
   end MyAdd;
end Caller;

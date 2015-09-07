with Parent.Public1.Public2;
package body Parent is

   procedure Square (Value : in out Parent_Int) is
   begin
      Value := Value ** 2;
   end Square;

end Parent;

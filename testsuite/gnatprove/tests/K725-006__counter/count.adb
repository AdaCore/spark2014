with Tab; pragma Elaborate (Tab);
with Other;
package body Count is
   package Key_Value_Table is new Tab (Integer);

   function Key (Position : Positive) return Integer is
   begin
      if Position <= Other.Table then
         return Key_Value_Table.Table;
      end if;
      return 0;
   end Key;
end Count;

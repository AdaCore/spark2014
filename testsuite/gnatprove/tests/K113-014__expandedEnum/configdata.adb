with PrivTypes;

package body ConfigData
is

   function SetDefaults return PrivTypes.ClassT
   is
   begin
      return PrivTypes.Unmarked;
   end SetDefaults;

end ConfigData;


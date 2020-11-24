pragma Ada_2020;

package Version is

   function Release return String is ("");

   type Release_Callback is access function return String with
     Post => True;

   procedure Do_Nothing is null;

   type Do_Nothing_Callback is access procedure with
     Post => True;

   Next : Release_Callback := Release'Access;
   Next_2 : Do_Nothing_Callback := Do_Nothing'Access;

end Version;

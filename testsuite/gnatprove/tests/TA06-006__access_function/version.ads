pragma Ada_2020;

package Version is

   function Release return String is ("");

   type Release_Callback is access function return String with
     Post => True;

   Next : Release_Callback := Release'Access;

end Version;

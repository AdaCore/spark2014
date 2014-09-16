with Misc;
package body Other with SPARK_Mode => Off is

   procedure New_Widget (X : out Foo.Widget_T)
   is
      type T is record
         Valid : Boolean;
         W     : Foo.Widget_T;
      end record;
      Tmp : constant T := (Valid => True,
                           W     => Foo.Null_Widget);
   begin
      X := (Tmp.W.X, Misc.Misc_Const.Y);
   end New_Widget;

end Other;

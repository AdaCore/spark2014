with Gen;

package body Types with SPARK_Mode is

   package body Chi is
      function "=" (Left, Right : Child) return Boolean is
         use Par;
         package My_Gen is new Gen (Root'Class);
         use My_Gen;
      begin
         Test (Left);
         return Left.I = Right.I and then Left.J = Right.J;
      end "=";
   end Chi;

end Types;

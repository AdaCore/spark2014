pragma SPARK_Mode;

with SK;

with Gen; pragma Elaborate_All (Gen);

package Test
is

   package P is new Gen (Elem => SK.Subject_State_Type);

end Test;

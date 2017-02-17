with Gen;
pragma Elaborate_All(Gen);
package Isnew is pragma SPARK_Mode (On);
   package G is new Gen (Integer);
end Isnew;

pragma Spark_Mode;
package Bug0 is

   procedure Bug (S : in out String) with
   Post => S = S'Old;

end Bug0;

with Discr; use Discr;
package Bad with SPARK_Mode is
   function Too_Small return Integer is (0);
   P1 : T (0);
end Bad;


package PP
with SPARK_Mode => Off
is

   type ENUM is (A);
   subtype SUBENUM is ENUM range A .. A;

end PP;

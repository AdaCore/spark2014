--  generic
--     Number_Of_Joints : Positive := 2;
package homothetical with SPARK_Mode Is

   N : constant Positive := 2;

   subtype Joint_Index is Positive range 1 .. N;

   type Joint_Values is array (Joint_Index) of Float;

   procedure
   homothetical(
                -- Distance to by travelled by joint j.
                D : in Joint_Values;
                kv : in Joint_Values;
                ka : in Joint_Values;
                kvmax : out Joint_Values;
                kamax : out Joint_Values)
   with
     Pre => (for all j in Joint_Index'Range =>
               D(j) /= 0.0 and
               kv(j) > 0.0 and
               ka(j) > 0.0),
     Post => (for all j in Joint_Index'Range =>
                kvmax(j) > 0.0 and kvmax(j) <= kv(j) and
                kamax(j) > 0.0 and kamax(j) <= ka(j));

end;

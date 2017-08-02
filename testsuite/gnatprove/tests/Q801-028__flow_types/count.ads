pragma SPARK_Mode (On);

package Count is

   procedure resetCounter (counter : out Integer)
     with
       Global	=> null,
       Post   	=> counter = 0;

   procedure addOne (counter: in out Integer)
     with
       Global	=> null,
       Depends	=> (counter => counter),
       Pre	=> (counter >= Integer'First) AND (counter < Integer'Last),
       Post	=> counter = counter'Old + 1;

end Count;

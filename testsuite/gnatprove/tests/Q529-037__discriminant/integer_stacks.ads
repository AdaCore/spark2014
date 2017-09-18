pragma SPARK_Mode (On);

with Bounded_Stacks; pragma Elaborate_All (Bounded_Stacks);
package Integer_Stacks is new Bounded_Stacks (Element => Integer, Default_Element => 0);

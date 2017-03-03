pragma SPARK_Mode;
package vol is

  procedure set_a(idx : in integer;
                  val : in integer );

  procedure get_a( idx : in integer;
                   val : out integer );

end vol;

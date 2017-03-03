pragma SPARK_Mode;
package body vol is

  b : array(1..10) of float;

  a : array(1..10) of integer;
  pragma volatile(a);
  for a'address use b'address;

  procedure set_a(idx : in integer;
                  val : in integer )
  is
  begin
    a(idx) := val;
  end set_a;

  procedure get_a( idx : in integer;
                   val : out integer )
  is
  begin
    val := a(idx);
  end get_a;

end vol;

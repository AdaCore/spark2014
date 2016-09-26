with Foo;

package Bar with SPARK_Mode
is
   procedure Get_Data (X : out Integer)
      with Global => (Input  => Foo.State,
                      In_Out => Foo.Atomics_State);

end Bar;

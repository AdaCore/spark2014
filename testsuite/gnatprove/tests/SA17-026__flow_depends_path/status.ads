with Time;

package Status
   with Abstract_State => (S, mode)
is
   procedure update
     with Global  => (Input  => mode,
                      In_Out => (S, Time.S)),
          Depends => (S      => (S, mode, Time.S),
                      Time.s => Time.s);
end Status;

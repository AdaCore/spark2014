generic
package GP with Abstract_State => State, Initializes => State is
   procedure Flip with Global => (In_Out => State);
end;

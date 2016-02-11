generic
   type T is private;
package GP with
   Abstract_State => (State,
                      (Atomic_State with External)),
   Elaborate_Body
is
end GP;

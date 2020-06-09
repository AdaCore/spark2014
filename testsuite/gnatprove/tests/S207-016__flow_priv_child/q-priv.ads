private package Q.Priv
 -- with Abstract_State => (Priv_State with Part_Of => Q.State)
is
   --  This is a private package, so its state and the state of its children
   --  should be Part_Of the parent's state.
   --  However since this package has no state of its own,
   --  declaration of _any_ state leads to errors.
end;

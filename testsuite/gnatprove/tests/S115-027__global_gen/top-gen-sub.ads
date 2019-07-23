generic
package Top.Gen.Sub
with
   Abstract_State => null
is

   type State_Type is private;

   procedure Update (S : in out State_Type);

private

   type State_Type is new Top.State_Type;

end Top.Gen.Sub;

with Generic_Parent; pragma Elaborate_All (Generic_Parent);
with Types;
package This_Parent is new Generic_Parent(Types.Digit_Range);

with Ada.Finalization;
with Named_Lists;

package Root is

   package Lists is new Named_Lists (Ada.Finalization.Controlled);

end Root;

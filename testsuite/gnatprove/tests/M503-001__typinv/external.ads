with Reentrancy; use Reentrancy;

package External is

   procedure Create (X : out T);

   procedure Update (X : in out T);

   function Get (X : T) return Integer;

end External;

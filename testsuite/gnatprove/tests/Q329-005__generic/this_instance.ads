with Generic_Parent.Child_Instance; pragma Elaborate_All (Generic_Parent.Child_Instance);
with This_Parent;
with Types;
package This_Instance is new This_Parent.Child_Instance;

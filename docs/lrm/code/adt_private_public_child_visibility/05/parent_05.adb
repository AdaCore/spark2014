with Parent_05.Private_Child_A_05,   -- OK
     Parent_05.Public_Child_A_05;    -- error, public children not visible
package body Parent_05
is
  function F return Integer is separate;
end Parent_05;

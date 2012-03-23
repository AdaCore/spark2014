pragma Ada_12;

package P is
  type Index is new Integer range 0 .. 100;

  subtype Element is Integer range 1 .. 10;

  type Vector is array (Index range <>) of Element;

  function Sum (X : Vector; Lo : Index; Hi : Index) return Integer is
	(if Lo > Hi or else X'First > Lo or else X'Last > Hi then 0
	 else (Sum (X, Lo, Hi - 1) + X (Hi)));

end P;

from typing import Any
from typing import Iterable

from textual.coordinate import Coordinate
from textual.widgets import DataTable
from textual.widgets._data_table import RowDoesNotExist
from textual.widgets._data_table import RowKey


class CustomDataTable(DataTable[Any]):
    """
    A DataTable that has removable rows. As of Textual version 0.19.1, this has not been added
    and Martin is waiting for a PR to have it merged in.
    """

    def remove_row(self, row_key: RowKey):
        """Remove a row.
        Args:
            row_key: Key describing the specific row to remove
        Returns:
            The `DataTable` instance.
        """

        if row_key not in self._row_locations:
            raise RowDoesNotExist(f"The row key {row_key!r} does not exist!")

        row_index = self._row_locations.get(row_key)
        self._require_update_dimensions = True

        if row_index == self.hover_row:
            self.hover_coordinate = Coordinate(max(0, row_index - 1), self.hover_column)
        self.cursor_coordinate: Coordinate
        if self.cursor_coordinate.row == row_index:
            self.cursor_coordinate = Coordinate(
                max(0, row_index - 1), self.cursor_coordinate.column
            )

        row_count = self.row_count
        del self._row_locations[row_key]
        del self.rows[row_key]
        del self._data[row_key]

        for after_row_index in range(row_index + 1, row_count):
            after_row = self._row_locations.get_key(after_row_index)
            self._row_locations[after_row] = after_row_index - 1

        if row_key in self._new_rows:
            self._new_rows.remove(row_key)

        self._update_count += 1
        self.check_idle()

    def remove_rows(self, row_keys: Iterable[RowKey]):
        """Remove a number of rows.
        Args:
            row_keys: Iterable of keys. A key describes the specific row to remove.
        Returns:
            The `DataTable` instance.
        """
        for row_key in row_keys:
            self.remove_row(row_key)

    pass

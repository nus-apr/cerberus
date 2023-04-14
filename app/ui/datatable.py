from typing import Any
from typing import Iterable
from typing import Self

from textual.widgets import DataTable
from textual.widgets._data_table import RowDoesNotExist
from textual.widgets._data_table import RowKey


class CustomDataTable(DataTable[Any]):
    """
    A DataTable that has removable rows. As of Textual version 0.19.0, this has not been added
    and Martin is waiting for a PR to have it merged in.
    """

    def remove_row(self, row_key: RowKey) -> Self:
        """Remove a row.
        Args:
            row_key: Key describing the specific row to remove
        Returns:
            The `DataTable` instance.
        """
        if row_key not in self._row_locations:
            raise RowDoesNotExist(f"The row key {row_key!r} already exists.")

        del self._row_locations[row_key]
        del self._data[row_key]
        del self.rows[row_key]

        # cell_now_unavailable = self.row_count == 0
        # visible_cursor = self.show_cursor and self.cursor_type != "none"
        # if cell_now_unavailable and visible_cursor:
        #     self._highlight_cursor()

        self._update_count -= 1
        # self.refresh()
        self.check_idle()
        return self

    def remove_rows(self, row_keys: Iterable[RowKey]) -> Self:
        """Remove a number of rows.
        Args:
            row_keys: Iterable of keys. A key describes the specific row to remove.
        Returns:
            The `DataTable` instance.
        """
        for row_key in row_keys:
            self.remove_row(row_key)
        return self

    pass

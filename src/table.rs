//! The [`Table`] widget is used to display multiple rows and columns in a grid and allows selecting
//! one or multiple cells.

use ratatui_core::buffer::Buffer;
use ratatui_core::layout::{Constraint, Flex, Layout, Rect};
use ratatui_core::style::{Style, Styled};
use ratatui_core::text::{Line, Text};
use ratatui_core::widgets::{StatefulWidget, Widget};
pub use ratatui_widgets::block::{Block, BlockExt as _};
use ratatui_widgets::scrollbar::{Scrollbar, ScrollbarOrientation, ScrollbarState};

use crate::highlight_spacing::HighlightSpacing;
use crate::state::State;

/// A widget to display data in formatted columns.
///
/// A `Table` is a collection of rows, each composed of cells:
///
/// You can construct a [`Table`] using [`Table::new`] and then chain
/// builder style methods to set the desired properties.
///
/// Table cells can be aligned, for more details see [`Line`].
///
/// [`Table`] implements [`Widget`] and so it can be drawn using `Frame::render_widget`.
///
/// [`Table`] is also a [`StatefulWidget`], which means you can use it with [`State`] to allow
/// the user to scroll through the rows and select one of them. When rendering a [`Table`] with a
/// [`State`], the selected row, column and cell will be highlighted. If the selected row is
/// not visible (based on the offset), the table will be scrolled to make the selected row visible.
///
/// Note: Highlight styles are applied in the following order: Row, Column, Cell.
///
/// # Example
///
/// ```rust
/// use ratatui::layout::Constraint;
/// use ratatui::style::{Style, Stylize};
/// use ratatui::text::Line;
/// use ratatui::widgets::Block;
/// use ratatui_logline_table::Table;
///
/// let rows = [["Cell1", "Cell2", "Cell3"]];
/// // Columns widths are constrained in the same way as Layout...
/// let widths = [
///     Constraint::Length(5),
///     Constraint::Length(5),
///     Constraint::Length(10),
/// ];
/// let table = Table::new(&rows, widths, |_index, line| {
///     [Line::raw(line[0]), Line::raw(line[1]), Line::raw(line[2])]
/// })
/// // ...and they can be separated by a fixed spacing.
/// .column_spacing(1)
/// // You can set the style of the entire Table.
/// .style(Style::new().blue())
/// // It has an optional header, which is simply a Row always visible at the top.
/// .header([Line::raw("Col1"), Line::raw("Col2"), Line::raw("Col3")])
/// .header_style(Style::new().bold())
/// // As any other widget, a Table can be wrapped in a Block.
/// .block(Block::new().title("Table"))
/// // The selected row and its content can also be styled.
/// .row_highlight_style(Style::new().reversed())
/// // ...and potentially show a symbol in front of the selection.
/// .highlight_symbol(">>");
/// ```
///
/// `Table` also implements the [`Styled`] trait, which means you can use style shorthands from
/// the [`Stylize`] trait to set the style of the widget more concisely.
///
/// ```rust
/// use ratatui::style::Stylize;
/// # use ratatui::{layout::Constraint, text::Line};
/// # use ratatui_logline_table::Table;
/// # let rows = [["Cell1", "Cell2"]];
/// # let widths = [Constraint::Length(5), Constraint::Length(5)];
/// # let to_row = |_index, line: &[&'static str; 2]| [Line::raw(line[0]), Line::raw(line[1])];
/// let table = Table::new(&rows, widths, to_row).red().italic();
/// ```
///
/// # Stateful example
///
/// `Table` is a [`StatefulWidget`], which means you can use it with [`State`] to allow the
/// user to scroll through the rows and select one of them.
///
/// ```rust
/// use ratatui::Frame;
/// use ratatui::layout::{Constraint, Rect};
/// use ratatui::style::{Style, Stylize};
/// use ratatui::text::Line;
/// use ratatui::widgets::Block;
/// use ratatui_logline_table::{State, Table};
///
/// # fn ui(frame: &mut Frame) {
/// # let area = Rect::ZERO;
/// // Note: State should be stored in your application state (not constructed in your render
/// // method) so that the selected row is preserved across renders
/// let mut state = State::default();
/// let rows = [
///     ["Row11", "Row12", "Row13"],
///     ["Row21", "Row22", "Row23"],
///     ["Row31", "Row32", "Row33"],
/// ];
/// let widths = [
///     Constraint::Length(5),
///     Constraint::Length(5),
///     Constraint::Length(10),
/// ];
/// let table = Table::new(&rows, widths, |_index, line| {
///     [Line::raw(line[0]), Line::raw(line[1]), Line::raw(line[2])]
/// })
/// .block(Block::new().title("Table"))
/// .row_highlight_style(Style::new().reversed())
/// .highlight_symbol(">>");
///
/// frame.render_stateful_widget(table, area, &mut state);
/// # }
/// ```
///
/// [`Stylize`]: ratatui::style::Stylize
#[must_use]
pub struct Table<'a, const COLUMNS: usize, Logline> {
    lines: &'a [Logline],

    to_row: Box<dyn Fn(usize, &'a Logline) -> [Line<'a>; COLUMNS]>,

    /// Optional header
    header: Option<[Line<'a>; COLUMNS]>,

    /// Optional footer
    footer: Option<[Line<'a>; COLUMNS]>,

    /// Width constraints for each column
    widths: [Constraint; COLUMNS],

    /// Space between each column
    column_spacing: u16,

    /// A block to wrap the widget in
    block: Option<Block<'a>>,

    /// Base style for the widget
    style: Style,

    header_style: Style,

    footer_style: Style,

    /// Style used to render the selected row
    row_highlight_style: Style,

    /// Symbol in front of the selected row
    highlight_symbol: Text<'a>,

    /// Decides when to allocate spacing for the row selection
    highlight_spacing: HighlightSpacing,

    /// Controls how to distribute extra space among the columns
    flex: Flex,
}

impl<'a, const COLUMNS: usize, Logline> Table<'a, COLUMNS, Logline> {
    /// Creates a new [`Table`] widget with the given rows.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ratatui::layout::Constraint;
    /// use ratatui::text::Line;
    /// use ratatui_logline_table::Table;
    ///
    /// let rows = [["Cell1", "Cell2"], ["Cell3", "Cell4"]];
    /// let widths = [Constraint::Length(5), Constraint::Length(5)];
    /// let table = Table::new(&rows, widths, |_index, line| {
    ///     [Line::raw(line[0]), Line::raw(line[1])]
    /// });
    /// ```
    pub fn new<ToRowFn>(
        lines: &'a [Logline],
        widths: [Constraint; COLUMNS],
        to_row: ToRowFn,
    ) -> Self
    where
        ToRowFn: Fn(usize, &'a Logline) -> [Line<'a>; COLUMNS] + 'static,
    {
        ensure_percentages_less_than_100(&widths);
        Self {
            lines,
            to_row: Box::new(to_row),
            widths,
            header: None,
            footer: None,
            column_spacing: 1,
            block: None,
            style: Style::new(),
            header_style: Style::new(),
            footer_style: Style::new(),
            row_highlight_style: Style::new(),
            highlight_symbol: Text::default(),
            highlight_spacing: HighlightSpacing::default(),
            flex: Flex::Start,
        }
    }

    /// Sets the header row which will be displayed at the top of the [`Table`]
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use ratatui::{layout::Constraint, text::Line};
    /// # use ratatui_logline_table::Table;
    /// # let rows = [["Cell1", "Cell2"]];
    /// # let widths = [Constraint::Length(5), Constraint::Length(5)];
    /// # let to_row = |_index, line: &[&'static str; 2]| [Line::raw(line[0]), Line::raw(line[1])];
    /// let header = [Line::raw("Header Cell 1"), Line::raw("Header Cell 2")];
    /// let table = Table::new(&rows, widths, to_row).header(header);
    /// ```
    pub fn header(mut self, header: [Line<'a>; COLUMNS]) -> Self {
        self.header = Some(header);
        self
    }

    /// Sets the footer row which will be displayed at the bottom of the [`Table`]
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use ratatui::{layout::Constraint, text::Line};
    /// # use ratatui_logline_table::Table;
    /// # let rows = [["Cell1", "Cell2"]];
    /// # let widths = [Constraint::Length(5), Constraint::Length(5)];
    /// # let to_row = |_index, line: &[&'static str; 2]| [Line::raw(line[0]), Line::raw(line[1])];
    /// let footer = [Line::raw("Footer Cell 1"), Line::raw("Footer Cell 2")];
    /// let table = Table::new(&rows, widths, to_row).footer(footer);
    /// ```
    pub fn footer(mut self, footer: [Line<'a>; COLUMNS]) -> Self {
        self.footer = Some(footer);
        self
    }

    pub const fn header_style(mut self, style: Style) -> Self {
        self.header_style = style;
        self
    }

    pub const fn footer_style(mut self, style: Style) -> Self {
        self.footer_style = style;
        self
    }

    /// Set the spacing between columns
    pub const fn column_spacing(mut self, spacing: u16) -> Self {
        self.column_spacing = spacing;
        self
    }

    /// Wraps the table with a custom [`Block`] widget.
    ///
    /// The `block` parameter is of type [`Block`]. This holds the specified block to be
    /// created around the [`Table`]
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ratatui::widgets::Block;
    /// # use ratatui::{layout::Constraint, text::Line};
    /// # use ratatui_logline_table::Table;
    /// # let rows = [["Cell1", "Cell2"]];
    /// # let widths = [Constraint::Length(5), Constraint::Length(5)];
    /// # let to_row = |_index, line: &[&'static str; 2]| [Line::raw(line[0]), Line::raw(line[1])];
    /// let block = Block::bordered().title("Table");
    /// let table = Table::new(&rows, widths, to_row).block(block);
    /// ```
    pub fn block(mut self, block: Block<'a>) -> Self {
        self.block = Some(block);
        self
    }

    /// Sets the base style of the widget
    ///
    /// `style` accepts any type that is convertible to [`Style`] (e.g. [`Style`], [`Color`], or
    /// your own type that implements [`Into<Style>`]).
    ///
    /// All text rendered by the widget will use this style, unless overridden by [`Block::style`],
    /// or the styles of cell's content.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use ratatui::layout::Constraint;
    /// use ratatui::style::{Style, Stylize};
    /// use ratatui::text::Line;
    /// use ratatui_logline_table::Table;
    ///
    /// # let rows = [["Cell1", "Cell2"]];
    /// # let widths = [Constraint::Length(5), Constraint::Length(5)];
    /// # let to_row = |_index, line: &[&'static str; 2]| [Line::raw(line[0]), Line::raw(line[1])];
    /// let table = Table::new(&rows, widths, to_row).style(Style::new().red().italic());
    /// ```
    ///
    /// `Table` also implements the [`Styled`] trait, which means you can use style shorthands from
    /// the [`Stylize`] trait to set the style of the widget more concisely.
    ///
    /// ```rust
    /// use ratatui::layout::Constraint;
    /// use ratatui::style::Stylize;
    /// use ratatui::text::Line;
    /// use ratatui_logline_table::Table;
    ///
    /// # let rows = [["Cell1", "Cell2"]];
    /// # let widths = [Constraint::Length(5), Constraint::Length(5)];
    /// # let to_row = |_index, line: &[&'static str; 2]| [Line::raw(line[0]), Line::raw(line[1])];
    /// let table = Table::new(&rows, widths, to_row).red().italic();
    /// ```
    ///
    /// [`Color`]: ratatui::style::Color
    /// [`Stylize`]: ratatui::style::Stylize
    pub fn style<S: Into<Style>>(mut self, style: S) -> Self {
        self.style = style.into();
        self
    }

    /// Set the style of the selected row
    ///
    /// `style` accepts any type that is convertible to [`Style`] (e.g. [`Style`], [`Color`], or
    /// your own type that implements [`Into<Style>`]).
    ///
    /// This style will be applied to the entire row, including the selection symbol if it is
    /// displayed, and will override any style set on the row or on the individual cells.
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use ratatui::{layout::Constraint, style::{Style, Stylize}, text::Line};
    /// # use ratatui_logline_table::Table;
    /// # let rows = [["Cell1", "Cell2"]];
    /// # let widths = [Constraint::Length(5), Constraint::Length(5)];
    /// # let to_row = |_index, line: &[&'static str; 2]| [Line::raw(line[0]), Line::raw(line[1])];
    /// let table = Table::new(&rows, widths, to_row).row_highlight_style(Style::new().red().italic());
    /// ```
    /// [`Color`]: ratatui::style::Color
    pub fn row_highlight_style<S: Into<Style>>(mut self, highlight_style: S) -> Self {
        self.row_highlight_style = highlight_style.into();
        self
    }

    /// Set the symbol to be displayed in front of the selected row
    ///
    /// # Examples
    ///
    /// ```rust
    /// # use ratatui::{layout::Constraint, text::Line};
    /// # use ratatui_logline_table::Table;
    /// # let rows = [["Cell1", "Cell2"]];
    /// # let widths = [Constraint::Length(5), Constraint::Length(5)];
    /// # let to_row = |_index, line: &[&'static str; 2]| [Line::raw(line[0]), Line::raw(line[1])];
    /// let table = Table::new(&rows, widths, to_row).highlight_symbol(">>");
    /// ```
    pub fn highlight_symbol<T: Into<Text<'a>>>(mut self, highlight_symbol: T) -> Self {
        self.highlight_symbol = highlight_symbol.into();
        self
    }

    /// Set when to show the highlight spacing
    ///
    /// The highlight spacing is the spacing that is allocated for the selection symbol column (if
    /// enabled) and is used to shift the table when a row is selected. This method allows you to
    /// configure when this spacing is allocated.
    ///
    /// - [`HighlightSpacing::Always`] will always allocate the spacing, regardless of whether a row
    ///   is selected or not. This means that the table will never change size, regardless of if a
    ///   row is selected or not.
    /// - [`HighlightSpacing::WhenSelected`] will only allocate the spacing if a row is selected.
    ///   This means that the table will shift when a row is selected. This is the default setting
    ///   for backwards compatibility, but it is recommended to use `HighlightSpacing::Always` for a
    ///   better user experience.
    /// - [`HighlightSpacing::Never`] will never allocate the spacing, regardless of whether a row
    ///   is selected or not. This means that the highlight symbol will never be drawn.
    pub const fn highlight_spacing(mut self, value: HighlightSpacing) -> Self {
        self.highlight_spacing = value;
        self
    }

    /// Set how extra space is distributed amongst columns.
    ///
    /// This determines how the space is distributed when the constraints are satisfied. By default,
    /// the extra space is not distributed at all.  But this can be changed to distribute all extra
    /// space to the last column or to distribute it equally.
    pub const fn flex(mut self, flex: Flex) -> Self {
        self.flex = flex;
        self
    }
}

impl<const COLUMNS: usize, Logline> Widget for Table<'_, COLUMNS, Logline> {
    fn render(self, area: Rect, buf: &mut Buffer) {
        Widget::render(&self, area, buf);
    }
}

impl<const COLUMNS: usize, Logline> Widget for &Table<'_, COLUMNS, Logline> {
    fn render(self, area: Rect, buf: &mut Buffer) {
        let mut state = State::new();
        StatefulWidget::render(self, area, buf, &mut state);
    }
}

impl<const COLUMNS: usize, Logline> StatefulWidget for Table<'_, COLUMNS, Logline> {
    type State = State;

    fn render(self, area: Rect, buf: &mut Buffer, state: &mut Self::State) {
        StatefulWidget::render(&self, area, buf, state);
    }
}

impl<const COLUMNS: usize, Logline> StatefulWidget for &Table<'_, COLUMNS, Logline> {
    type State = State;

    fn render(self, full_area: Rect, buf: &mut Buffer, state: &mut Self::State) {
        buf.set_style(full_area, self.style);
        if let Some(block) = &self.block {
            block.render(full_area, buf);
        }
        let table_area = self.block.inner_if_some(full_area);
        if table_area.is_empty() {
            state.last_row_area = Rect::ZERO;
            return;
        }

        state.last_biggest_index = self.lines.len().saturating_sub(1);

        if self.lines.is_empty() {
            state.selected = None;
        } else if state.selected.is_some_and(|row| row >= self.lines.len()) {
            state.selected = Some(state.last_biggest_index);
        }

        let selection_width = self.selection_width(state);
        let column_widths = self.get_column_widths(table_area.width, selection_width);
        let (header_area, rows_area, footer_area) = self.layout(table_area);

        state.last_row_area = rows_area;

        self.render_header(header_area, buf, &column_widths);

        self.render_rows(rows_area, buf, state, selection_width, &column_widths);

        self.render_footer(footer_area, buf, &column_widths);

        // Only render scrollbar when there is a border on the right
        if rows_area.right() < full_area.right() {
            let scrollbar = Scrollbar::new(ScrollbarOrientation::VerticalRight)
                .begin_symbol(None)
                .track_symbol(None)
                .end_symbol(None);
            let overscroll_workaround = self.lines.len().saturating_sub(rows_area.height as usize);
            let mut scrollbar_state = ScrollbarState::new(overscroll_workaround)
                .position(state.offset)
                // Should be available_height but with the current overscroll workaround this looks nicer
                .viewport_content_length(rows_area.height as usize);
            let scrollbar_area = Rect {
                // Inner height to be exactly as the content
                y: rows_area.y,
                height: rows_area.height,
                // Outer width to stay on the right border
                x: full_area.x,
                width: full_area.width,
            };
            scrollbar.render(scrollbar_area, buf, &mut scrollbar_state);
        }
    }
}

// private methods for rendering
impl<const COLUMNS: usize, Logline> Table<'_, COLUMNS, Logline> {
    /// Splits the table area into a header, rows area and a footer
    fn layout(&self, area: Rect) -> (Rect, Rect, Rect) {
        let header_height = u16::from(self.header.is_some());
        let footer_height = u16::from(self.footer.is_some());
        Layout::vertical([
            Constraint::Length(header_height),
            Constraint::Min(0),
            Constraint::Length(footer_height),
        ])
        .areas(area)
        .into()
    }

    fn render_header(&self, area: Rect, buf: &mut Buffer, column_widths: &[(u16, u16)]) {
        if let Some(ref header) = self.header {
            buf.set_style(area, self.header_style);
            for ((x, width), cell) in column_widths.iter().zip(header.iter()) {
                cell.render(Rect::new(area.x + x, area.y, *width, area.height), buf);
            }
        }
    }

    fn render_footer(&self, area: Rect, buf: &mut Buffer, column_widths: &[(u16, u16)]) {
        if let Some(ref footer) = self.footer {
            buf.set_style(area, self.footer_style);
            for ((x, width), cell) in column_widths.iter().zip(footer.iter()) {
                cell.render(Rect::new(area.x + x, area.y, *width, area.height), buf);
            }
        }
    }

    fn render_rows(
        &self,
        area: Rect,
        buf: &mut Buffer,
        state: &mut State,
        selection_width: u16,
        columns_widths: &[(u16, u16)],
    ) {
        if self.lines.is_empty() {
            return;
        }

        // Scroll down offset as much as possible
        let offset_with_last_in_view = self.lines.len().saturating_sub(area.height as usize);
        let scroll_last_into_view = if let Some(selected) = state.selected {
            // Only scroll when the change will include both end and selection.
            // When the user manually scrolled away from the end keep the offset.
            selected >= offset_with_last_in_view
        } else {
            state.scroll_keeps_last_in_view || state.offset >= offset_with_last_in_view
        };
        if scroll_last_into_view {
            state.offset = offset_with_last_in_view;
            state.scroll_keeps_last_in_view = true;
        }

        let (start_index, end_index) = self.visible_rows(state, area);
        state.ensure_selected_in_view_on_next_render = false;
        state.offset = start_index;

        let mut selected_row_area = None;
        for (index, row) in self
            .lines
            .iter()
            .enumerate()
            .skip(start_index)
            .take(end_index - start_index)
        {
            let y = area.y + index.saturating_sub(start_index) as u16;
            let height = 1;
            let row_area = Rect { y, height, ..area };

            let is_selected = state.selected.is_some_and(|selected| selected == index);
            if selection_width > 0 && is_selected {
                let selection_area = Rect {
                    width: selection_width,
                    ..row_area
                };
                (&self.highlight_symbol).render(selection_area, buf);
            }
            let cells = (self.to_row)(index, row);
            for ((x, width), cell) in columns_widths.iter().copied().zip(cells.iter()) {
                cell.render(
                    Rect {
                        x: row_area.x + x,
                        width,
                        ..row_area
                    },
                    buf,
                );
            }
            if is_selected {
                selected_row_area = Some(row_area);
            }
        }

        if let Some(row_area) = selected_row_area {
            buf.set_style(row_area, self.row_highlight_style);
        }
    }

    /// Return the indexes of the visible rows.
    ///
    /// The algorithm works as follows:
    /// - start at the offset and calculate the height of the rows that can be displayed within the
    ///   area.
    /// - if the selected row is not visible, scroll the table to ensure it is visible.
    /// - if there is still space to fill then there's a partial row at the end which should be
    ///   included in the view.
    fn visible_rows(&self, state: &State, area: Rect) -> (usize, usize) {
        let mut start = state.offset.min(state.last_biggest_index);

        let ensure_index_in_view = state
            .selected
            .filter(|_| state.ensure_selected_in_view_on_next_render)
            .map(|selected| selected.min(state.last_biggest_index));

        if let Some(ensure_index_in_view) = ensure_index_in_view {
            start = start.min(ensure_index_in_view);
        }

        let mut height = area.height;
        let mut end = start
            .saturating_add(area.height as usize)
            .min(self.lines.len());

        if let Some(ensure_index_in_view) = ensure_index_in_view {
            // scroll down until the selected row is visible
            while ensure_index_in_view >= end {
                height = height.saturating_add(1);
                end += 1;
                while height > area.height {
                    height = height.saturating_sub(1);
                    start += 1;
                }
            }
        }

        // Include a partial row if there is space
        if height < area.height && end < self.lines.len() {
            end += 1;
        }

        (start, end)
    }

    /// Get all offsets and widths of all user specified columns.
    ///
    /// Returns (x, width). When self.widths is empty, it is assumed `.widths()` has not been called
    /// and a default of equal widths is returned.
    fn get_column_widths(&self, max_width: u16, selection_width: u16) -> Vec<(u16, u16)> {
        // this will always allocate a selection area
        let [_selection_area, columns_area] =
            Layout::horizontal([Constraint::Length(selection_width), Constraint::Fill(0)])
                .areas(Rect::new(0, 0, max_width, 1));
        let rects = Layout::horizontal(self.widths)
            .flex(self.flex)
            .spacing(self.column_spacing)
            .split(columns_area);
        rects.iter().map(|rect| (rect.x, rect.width)).collect()
    }

    /// Returns the width of the selection column if a row is selected, or the `highlight_spacing`
    /// is set to show the column always, otherwise 0.
    fn selection_width(&self, state: &State) -> u16 {
        let has_selection = state.selected.is_some();
        if self.highlight_spacing.should_add(has_selection) {
            self.highlight_symbol.width() as u16
        } else {
            0
        }
    }
}

fn ensure_percentages_less_than_100(widths: &[Constraint]) {
    for width in widths {
        if let Constraint::Percentage(percent) = width {
            assert!(
                *percent <= 100,
                "Percentages should be between 0 and 100 inclusively."
            );
        }
    }
}

impl<const COLUMNS: usize, Logline> Styled for Table<'_, COLUMNS, Logline> {
    type Item = Self;

    fn style(&self) -> Style {
        self.style
    }

    fn set_style<S: Into<Style>>(self, style: S) -> Self::Item {
        self.style(style)
    }
}

#[cfg(test)]
mod tests {
    use std::vec;

    use ratatui::style::{Color, Modifier, Style, Stylize as _};
    use ratatui::text::Line;
    use rstest::{fixture, rstest};

    use super::*;

    #[track_caller]
    fn str_to_row<'row, const N: usize>(_index: usize, row: &[&'row str; N]) -> [Line<'row>; N] {
        row.iter()
            .map(|text| Line::raw(*text))
            .collect::<Vec<_>>()
            .try_into()
            .expect("Should have correct COLUMNS")
    }

    #[test]
    fn new() {
        let lines = [[""]];
        let widths = [Constraint::Percentage(100)];
        let table = Table::new(&lines, widths, str_to_row);
        assert_eq!(table.lines, lines);
        assert_eq!(table.header, None);
        assert_eq!(table.footer, None);
        assert_eq!(table.widths, widths);
        assert_eq!(table.column_spacing, 1);
        assert_eq!(table.block, None);
        assert_eq!(table.style, Style::new());
        assert_eq!(table.row_highlight_style, Style::new());
        assert_eq!(table.highlight_symbol, Text::default());
        assert_eq!(table.highlight_spacing, HighlightSpacing::WhenSelected);
        assert_eq!(table.flex, Flex::Start);
    }

    #[test]
    fn column_spacing() {
        let lines = [[""]];
        let widths = [Constraint::Percentage(100)];
        let table = Table::new(&lines, widths, str_to_row).column_spacing(2);
        assert_eq!(table.column_spacing, 2);
    }

    #[test]
    fn block() {
        let block = Block::bordered().title("Table");
        let lines = [[""]];
        let widths = [Constraint::Percentage(100)];
        let table = Table::new(&lines, widths, str_to_row).block(block.clone());
        assert_eq!(table.block, Some(block));
    }

    #[test]
    fn header() {
        let lines = Vec::new();
        let header = [Line::raw("")];
        let table = Table::new(&lines, [Constraint::Fill(1)], str_to_row).header(header.clone());
        assert_eq!(table.header, Some(header));
    }

    #[test]
    fn footer() {
        let lines = Vec::new();
        let footer = [Line::raw("")];
        let table = Table::new(&lines, [Constraint::Fill(1)], str_to_row).footer(footer.clone());
        assert_eq!(table.footer, Some(footer));
    }

    #[test]
    fn row_highlight_style() {
        let style = Style::new().red().italic();
        let lines = [[""]];
        let widths = [Constraint::Percentage(100)];
        let table = Table::new(&lines, widths, str_to_row).row_highlight_style(style);
        assert_eq!(table.row_highlight_style, style);
    }

    #[test]
    fn highlight_symbol() {
        let lines = [[""]];
        let widths = [Constraint::Percentage(100)];
        let table = Table::new(&lines, widths, str_to_row).highlight_symbol(">>");
        assert_eq!(table.highlight_symbol, Text::from(">>"));
    }

    #[test]
    fn highlight_spacing() {
        let lines = [[""]];
        let widths = [Constraint::Percentage(100)];
        let table =
            Table::new(&lines, widths, str_to_row).highlight_spacing(HighlightSpacing::Always);
        assert_eq!(table.highlight_spacing, HighlightSpacing::Always);
    }

    #[test]
    #[should_panic = "Percentages should be between 0 and 100 inclusively"]
    fn table_invalid_percentages() {
        let lines = vec!["42"];
        let _ = Table::new(&lines, [Constraint::Percentage(110)], |_content, _index| {
            [Line::default()]
        });
    }

    #[cfg(test)]
    mod state {
        use ratatui::buffer::Buffer;
        use ratatui::layout::{Constraint, Rect};
        use ratatui::widgets::StatefulWidget;

        use super::*;

        #[fixture]
        fn table_buf() -> Buffer {
            Buffer::empty(Rect::new(0, 0, 10, 10))
        }

        #[rstest]
        fn empty(mut table_buf: Buffer) {
            let mut state = State::new();

            let rows = Vec::new();
            let widths = [Constraint::Percentage(100)];
            let table = Table::new(&rows, widths, str_to_row);
            state.select_first();
            StatefulWidget::render(table, table_buf.area, &mut table_buf, &mut state);
            assert_eq!(state.selected, None);
        }

        #[rstest]
        fn single_item(mut table_buf: Buffer) {
            let mut state = State::new();

            let widths = [Constraint::Percentage(100)];

            let items = vec![["Item 1"]];
            let table = Table::new(&items, widths, str_to_row);
            state.select_first();
            StatefulWidget::render(&table, table_buf.area, &mut table_buf, &mut state);
            assert_eq!(state.selected, Some(0));

            state.select_last();
            StatefulWidget::render(&table, table_buf.area, &mut table_buf, &mut state);
            assert_eq!(state.selected, Some(0));

            state.select_previous();
            StatefulWidget::render(&table, table_buf.area, &mut table_buf, &mut state);
            assert_eq!(state.selected, Some(0));

            state.select_next();
            StatefulWidget::render(&table, table_buf.area, &mut table_buf, &mut state);
            assert_eq!(state.selected, Some(0));
        }
    }

    #[cfg(test)]
    mod render {
        use ratatui::layout::Alignment;

        use super::*;

        #[test]
        fn render_empty_area() {
            let mut buf = Buffer::empty(Rect::new(0, 0, 15, 3));
            let rows = [["Cell1", "Cell2"]];
            let table = Table::new(&rows, [Constraint::Length(5); 2], str_to_row);
            Widget::render(table, Rect::new(0, 0, 0, 0), &mut buf);
            assert_eq!(buf, Buffer::empty(Rect::new(0, 0, 15, 3)));
        }

        #[test]
        fn render_with_block() {
            let mut buf = Buffer::empty(Rect::new(0, 0, 15, 3));
            let rows = [["Cell1", "Cell2"], ["Cell3", "Cell4"]];
            let block = Block::bordered().title("Block");
            let table = Table::new(&rows, [Constraint::Length(5); 2], str_to_row).block(block);
            Widget::render(table, Rect::new(0, 0, 15, 3), &mut buf);
            #[rustfmt::skip]
            let expected = Buffer::with_lines([
                "┌Block────────┐",
                "│Cell3 Cell4  █",
                "└─────────────┘",
            ]);
            assert_eq!(buf, expected);
        }

        #[test]
        fn render_with_header() {
            let mut buf = Buffer::empty(Rect::new(0, 0, 15, 3));
            let header = [Line::raw("Head1"), Line::raw("Head2")];
            let rows = [["Cell1", "Cell2"], ["Cell3", "Cell4"]];
            let table = Table::new(&rows, [Constraint::Length(5); 2], str_to_row).header(header);
            Widget::render(table, Rect::new(0, 0, 15, 3), &mut buf);
            #[rustfmt::skip]
            let expected = Buffer::with_lines([
                "Head1 Head2    ",
                "Cell1 Cell2    ",
                "Cell3 Cell4    ",
            ]);
            assert_eq!(buf, expected);
        }

        #[test]
        fn render_with_footer() {
            let mut buf = Buffer::empty(Rect::new(0, 0, 15, 3));
            let footer = [Line::raw("Foot1"), Line::raw("Foot2")];
            let rows = [["Cell1", "Cell2"], ["Cell3", "Cell4"]];
            let table = Table::new(&rows, [Constraint::Length(5); 2], str_to_row).footer(footer);
            Widget::render(table, Rect::new(0, 0, 15, 3), &mut buf);
            #[rustfmt::skip]
            let expected = Buffer::with_lines([
                "Cell1 Cell2    ",
                "Cell3 Cell4    ",
                "Foot1 Foot2    ",
            ]);
            assert_eq!(buf, expected);
        }

        #[test]
        fn render_with_header_and_footer() {
            let mut buf = Buffer::empty(Rect::new(0, 0, 15, 3));
            let header = [Line::raw("Head1"), Line::raw("Head2")];
            let footer = [Line::raw("Foot1"), Line::raw("Foot2")];
            let rows = [["Cell1", "Cell2"]];
            let table = Table::new(&rows, [Constraint::Length(5); 2], str_to_row)
                .header(header)
                .footer(footer);
            Widget::render(table, Rect::new(0, 0, 15, 3), &mut buf);
            #[rustfmt::skip]
            let expected = Buffer::with_lines([
                "Head1 Head2    ",
                "Cell1 Cell2    ",
                "Foot1 Foot2    ",
            ]);
            assert_eq!(buf, expected);
        }

        #[test]
        fn render_with_tall_row() {
            let mut buf = Buffer::empty(Rect::new(0, 0, 23, 3));
            let rows = vec![
                ["Cell1", "Cell2"],
                [
                    "Cell3-Line1\nCell3-Line2\nCell3-Line3",
                    "Cell4-Line1\nCell4-Line2\nCell4-Line3",
                ],
            ];
            let table = Table::new(&rows, [Constraint::Length(11); 2], str_to_row);
            Widget::render(table, Rect::new(0, 0, 23, 3), &mut buf);
            #[rustfmt::skip]
            let expected = Buffer::with_lines([
                "Cell1       Cell2      ",
                "Cell3-Line1 Cell4-Line1",
                "                       ",
            ]);
            assert_eq!(buf, expected);
        }

        #[test]
        fn render_with_alignment() {
            let mut buf = Buffer::empty(Rect::new(0, 0, 10, 3));
            let rows = vec![Alignment::Left, Alignment::Center, Alignment::Right];
            let table = Table::new(&rows, [Constraint::Percentage(100)], |_index, alignment| {
                [Line::raw(format!("{alignment:?}")).alignment(*alignment)]
            });
            Widget::render(table, Rect::new(0, 0, 10, 3), &mut buf);
            let expected = Buffer::with_lines(["Left      ", "  Center  ", "     Right"]);
            assert_eq!(buf, expected);
        }

        #[test]
        fn render_with_overflow_does_not_panic() {
            let mut buf = Buffer::empty(Rect::new(0, 0, 20, 3));
            let lines = Vec::new();
            let table = Table::new(&lines, [Constraint::Min(20); 1], str_to_row)
                .header([Line::raw("").alignment(Alignment::Right)])
                .footer([Line::raw("").alignment(Alignment::Right)]);
            Widget::render(table, Rect::new(0, 0, 20, 3), &mut buf);
        }

        #[test]
        fn render_with_selected() {
            let mut buf = Buffer::empty(Rect::new(0, 0, 15, 3));
            let rows = vec![["Cell1", "Cell2"], ["Cell3", "Cell4"]];
            let table = Table::new(&rows, [Constraint::Length(5); 2], str_to_row)
                .row_highlight_style(Style::new().red())
                .highlight_symbol(">>");
            let mut state = State::new();
            state.select(Some(0));
            StatefulWidget::render(table, Rect::new(0, 0, 15, 3), &mut buf, &mut state);
            let expected = Buffer::with_lines([
                ">>Cell1 Cell2  ".red(),
                "  Cell3 Cell4  ".into(),
                "               ".into(),
            ]);
            assert_eq!(buf, expected);
        }

        /// Note that this includes a regression test for a bug where the table would not render the
        /// correct rows when there is no selection.
        /// <https://github.com/ratatui/ratatui/issues/1179>
        #[rstest]
        #[case::no_selection_scrolls_down(None, 95, ["95", "96", "97", "98", "99"])]
        #[case::selection_before_offset(20, 20, ["20", "21", "22", "23", "24"])]
        #[case::selection_immediately_before_offset(49, 49, ["49", "50", "51", "52", "53"])]
        #[case::selection_at_start_of_offset(50, 50, ["50", "51", "52", "53", "54"])]
        #[case::selection_at_end_of_offset(54, 50, ["50", "51", "52", "53", "54"])]
        #[case::selection_immediately_after_offset(55, 51, ["51", "52", "53", "54", "55"])]
        #[case::selection_after_offset(80, 76, ["76", "77", "78", "79", "80"])]
        fn render_with_selection_and_offset<T: Into<Option<usize>>>(
            #[case] selected_row: T,
            #[case] expected_offset: usize,
            #[case] expected_items: [&str; 5],
        ) {
            // render 100 rows offset at 50, with a selected row
            let rows = (0..100).collect::<Vec<_>>();
            let table = Table::new(&rows, [Constraint::Length(2)], |number, _index| {
                [Line::raw(number.to_string())]
            });
            let mut buf = Buffer::empty(Rect::new(0, 0, 2, 5));
            let mut state = State::new().with_offset(50);
            state.select(selected_row.into());

            StatefulWidget::render(table, Rect::new(0, 0, 5, 5), &mut buf, &mut state);

            assert_eq!(buf, Buffer::with_lines(expected_items));
            assert_eq!(state.offset, expected_offset);
        }
    }

    // test how constraints interact with table column width allocation
    mod column_widths {
        use super::*;

        #[test]
        fn length_constraint() {
            use ratatui::layout::Constraint::Length;

            let lines = Vec::new();

            // without selection, more than needed width
            let table = Table::new(&lines, [Length(4), Length(4)], str_to_row);
            assert_eq!(table.get_column_widths(20, 0), [(0, 4), (5, 4)]);

            // with selection, more than needed width
            let table = Table::new(&lines, [Length(4), Length(4)], str_to_row);
            assert_eq!(table.get_column_widths(20, 3), [(3, 4), (8, 4)]);

            // without selection, less than needed width
            let table = Table::new(&lines, [Length(4), Length(4)], str_to_row);
            assert_eq!(table.get_column_widths(7, 0), [(0, 3), (4, 3)]);

            // with selection, less than needed width
            // <--------7px-------->
            // ┌────────┐x┌────────┐
            // │ (3, 2) │x│ (6, 1) │
            // └────────┘x└────────┘
            // column spacing (i.e. `x`) is always prioritized
            let table = Table::new(&lines, [Length(4), Length(4)], str_to_row);
            assert_eq!(table.get_column_widths(7, 3), [(3, 2), (6, 1)]);
        }

        #[test]
        fn max_constraint() {
            use ratatui::layout::Constraint::Max;

            let lines = Vec::new();

            // without selection, more than needed width
            let table = Table::new(&lines, [Max(4), Max(4)], str_to_row);
            assert_eq!(table.get_column_widths(20, 0), [(0, 4), (5, 4)]);

            // with selection, more than needed width
            let table = Table::new(&lines, [Max(4), Max(4)], str_to_row);
            assert_eq!(table.get_column_widths(20, 3), [(3, 4), (8, 4)]);

            // without selection, less than needed width
            let table = Table::new(&lines, [Max(4), Max(4)], str_to_row);
            assert_eq!(table.get_column_widths(7, 0), [(0, 3), (4, 3)]);

            // with selection, less than needed width
            let table = Table::new(&lines, [Max(4), Max(4)], str_to_row);
            assert_eq!(table.get_column_widths(7, 3), [(3, 2), (6, 1)]);
        }

        #[test]
        fn min_constraint() {
            use ratatui::layout::Constraint::Min;

            // in its currently stage, the "Min" constraint does not grow to use the possible
            // available length and enabling "expand_to_fill" will just stretch the last
            // constraint and not split it with all available constraints

            let lines = Vec::new();

            // without selection, more than needed width
            let table = Table::new(&lines, [Min(4), Min(4)], str_to_row);
            assert_eq!(table.get_column_widths(20, 0), [(0, 10), (11, 9)]);

            // with selection, more than needed width
            let table = Table::new(&lines, [Min(4), Min(4)], str_to_row);
            assert_eq!(table.get_column_widths(20, 3), [(3, 8), (12, 8)]);

            // without selection, less than needed width
            // allocates spacer
            let table = Table::new(&lines, [Min(4), Min(4)], str_to_row);
            assert_eq!(table.get_column_widths(7, 0), [(0, 3), (4, 3)]);

            // with selection, less than needed width
            // always allocates selection and spacer
            let table = Table::new(&lines, [Min(4), Min(4)], str_to_row);
            assert_eq!(table.get_column_widths(7, 3), [(3, 2), (6, 1)]);
        }

        #[test]
        fn percentage_constraint() {
            use ratatui::layout::Constraint::Percentage;

            let lines = Vec::new();

            // without selection, more than needed width
            let table = Table::new(&lines, [Percentage(30), Percentage(30)], str_to_row);
            assert_eq!(table.get_column_widths(20, 0), [(0, 6), (7, 6)]);

            // with selection, more than needed width
            let table = Table::new(&lines, [Percentage(30), Percentage(30)], str_to_row);
            assert_eq!(table.get_column_widths(20, 3), [(3, 5), (9, 5)]);

            // without selection, less than needed width
            // rounds from positions: [0.0, 0.0, 2.1, 3.1, 5.2, 7.0]
            let table = Table::new(&lines, [Percentage(30), Percentage(30)], str_to_row);
            assert_eq!(table.get_column_widths(7, 0), [(0, 2), (3, 2)]);

            // with selection, less than needed width
            // rounds from positions: [0.0, 3.0, 5.1, 6.1, 7.0, 7.0]
            let table = Table::new(&lines, [Percentage(30), Percentage(30)], str_to_row);
            assert_eq!(table.get_column_widths(7, 3), [(3, 1), (5, 1)]);
        }

        #[test]
        fn ratio_constraint() {
            use ratatui::layout::Constraint::Ratio;

            let lines = Vec::new();

            // without selection, more than needed width
            // rounds from positions: [0.00, 0.00, 6.67, 7.67, 14.33]
            let table = Table::new(&lines, [Ratio(1, 3), Ratio(1, 3)], str_to_row);
            assert_eq!(table.get_column_widths(20, 0), [(0, 7), (8, 6)]);

            // with selection, more than needed width
            // rounds from positions: [0.00, 3.00, 10.67, 17.33, 20.00]
            let table = Table::new(&lines, [Ratio(1, 3), Ratio(1, 3)], str_to_row);
            assert_eq!(table.get_column_widths(20, 3), [(3, 6), (10, 5)]);

            // without selection, less than needed width
            // rounds from positions: [0.00, 2.33, 3.33, 5.66, 7.00]
            let table = Table::new(&lines, [Ratio(1, 3), Ratio(1, 3)], str_to_row);
            assert_eq!(table.get_column_widths(7, 0), [(0, 2), (3, 3)]);

            // with selection, less than needed width
            // rounds from positions: [0.00, 3.00, 5.33, 6.33, 7.00, 7.00]
            let table = Table::new(&lines, [Ratio(1, 3), Ratio(1, 3)], str_to_row);
            assert_eq!(table.get_column_widths(7, 3), [(3, 1), (5, 2)]);
        }

        /// When more width is available than requested, the behavior is controlled by flex
        #[test]
        fn underconstrained_flex() {
            use ratatui::layout::Constraint::Min;

            let lines = Vec::new();

            let table = Table::new(&lines, [Min(10), Min(10), Min(1)], str_to_row);
            assert_eq!(
                table.get_column_widths(62, 0),
                &[(0, 20), (21, 20), (42, 20)]
            );

            let table =
                Table::new(&lines, [Min(10), Min(10), Min(1)], str_to_row).flex(Flex::Legacy);
            assert_eq!(
                table.get_column_widths(62, 0),
                &[(0, 10), (11, 10), (22, 40)]
            );

            let table =
                Table::new(&lines, [Min(10), Min(10), Min(1)], str_to_row).flex(Flex::SpaceBetween);
            assert_eq!(
                table.get_column_widths(62, 0),
                &[(0, 20), (21, 20), (42, 20)]
            );
        }

        #[track_caller]
        fn test_table_with_selection<'line, Lines>(
            highlight_spacing: HighlightSpacing,
            columns: u16,
            spacing: u16,
            selection: Option<usize>,
            expected: Lines,
        ) where
            Lines: IntoIterator,
            Lines::Item: Into<Line<'line>>,
        {
            let lines = [["ABCDE", "12345"]];
            let table = Table::new(&lines, [Constraint::Fill(1); 2], str_to_row)
                .highlight_spacing(highlight_spacing)
                .highlight_symbol(">>>")
                .column_spacing(spacing);
            let area = Rect::new(0, 0, columns, 3);
            let mut buf = Buffer::empty(area);
            let mut state = State::new();
            state.select(selection);
            StatefulWidget::render(table, area, &mut buf, &mut state);
            assert_eq!(buf, Buffer::with_lines(expected));
        }

        #[test]
        fn excess_area_highlight_symbol_and_column_spacing_allocation() {
            // no highlight_symbol rendered ever
            test_table_with_selection(
                HighlightSpacing::Never,
                15,   // width
                0,    // spacing
                None, // selection
                [
                    "ABCDE   12345  ", /* default layout is Flex::Start but columns length
                                        * constraints are calculated as `max_area / n_columns`,
                                        * i.e. they are distributed amongst available space */
                    "               ", // row 2
                    "               ", // row 3
                ],
            );

            let lines = [["ABCDE", "12345"]];
            let table =
                Table::new(&lines, [Constraint::Length(5); 2], str_to_row).column_spacing(0);
            let area = Rect::new(0, 0, 15, 3);
            let mut buf = Buffer::empty(area);
            Widget::render(table, area, &mut buf);
            let expected = Buffer::with_lines([
                "ABCDE12345     ", /* As reference, this is what happens when you manually
                                    * specify widths */
                "               ", // row 2
                "               ", // row 3
            ]);
            assert_eq!(buf, expected);

            // no highlight_symbol rendered ever
            test_table_with_selection(
                HighlightSpacing::Never,
                15,      // width
                0,       // spacing
                Some(0), // selection
                [
                    "ABCDE   12345  ", // row 1
                    "               ", // row 2
                    "               ", // row 3
                ],
            );

            // no highlight_symbol rendered because no selection is made
            test_table_with_selection(
                HighlightSpacing::WhenSelected,
                15,   // width
                0,    // spacing
                None, // selection
                [
                    "ABCDE   12345  ", // row 1
                    "               ", // row 2
                    "               ", // row 3
                ],
            );
            // highlight_symbol rendered because selection is made
            test_table_with_selection(
                HighlightSpacing::WhenSelected,
                15,      // width
                0,       // spacing
                Some(0), // selection
                [
                    ">>>ABCDE 12345 ", // row 1
                    "               ", // row 2
                    "               ", // row 3
                ],
            );

            // highlight_symbol always rendered even no selection is made
            test_table_with_selection(
                HighlightSpacing::Always,
                15,   // width
                0,    // spacing
                None, // selection
                [
                    "   ABCDE 12345 ", // row 1
                    "               ", // row 2
                    "               ", // row 3
                ],
            );

            // no highlight_symbol rendered because no selection is made
            test_table_with_selection(
                HighlightSpacing::Always,
                15,      // width
                0,       // spacing
                Some(0), // selection
                [
                    ">>>ABCDE 12345 ", // row 1
                    "               ", // row 2
                    "               ", // row 3
                ],
            );
        }

        #[allow(clippy::too_many_lines)]
        #[test]
        fn insufficient_area_highlight_symbol_and_column_spacing_allocation() {
            // column spacing is prioritized over every other constraint
            test_table_with_selection(
                HighlightSpacing::Never,
                10,   // width
                1,    // spacing
                None, // selection
                [
                    "ABCDE 1234", // spacing is prioritized and column is cut
                    "          ", // row 2
                    "          ", // row 3
                ],
            );
            test_table_with_selection(
                HighlightSpacing::WhenSelected,
                10,   // width
                1,    // spacing
                None, // selection
                [
                    "ABCDE 1234", // spacing is prioritized and column is cut
                    "          ", // row 2
                    "          ", // row 3
                ],
            );

            // this test checks that space for highlight_symbol space is always allocated.
            // this test also checks that space for column is allocated.
            //
            // Space for highlight_symbol is allocated first by splitting horizontal space
            // into highlight_symbol area and column area.
            // Then in a separate step, column widths are calculated.
            // column spacing is prioritized when column widths are calculated and last column here
            // ends up with just 1 wide
            test_table_with_selection(
                HighlightSpacing::Always,
                10,   // width
                1,    // spacing
                None, // selection
                [
                    "   ABC 123", // highlight_symbol and spacing are prioritized
                    "          ", // row 2
                    "          ", // row 3
                ],
            );

            // the following are specification tests
            test_table_with_selection(
                HighlightSpacing::Always,
                9,    // width
                1,    // spacing
                None, // selection
                [
                    "   ABC 12", // highlight_symbol and spacing are prioritized
                    "         ", // row 2
                    "         ", // row 3
                ],
            );
            test_table_with_selection(
                HighlightSpacing::Always,
                8,    // width
                1,    // spacing
                None, // selection
                [
                    "   AB 12", // highlight_symbol and spacing are prioritized
                    "        ", // row 2
                    "        ", // row 3
                ],
            );
            test_table_with_selection(
                HighlightSpacing::Always,
                7,    // width
                1,    // spacing
                None, // selection
                [
                    "   AB 1", // highlight_symbol and spacing are prioritized
                    "       ", // row 2
                    "       ", // row 3
                ],
            );

            let lines = [["ABCDE", "12345"]];

            let table = Table::new(&lines, [Constraint::Fill(1); 2], str_to_row)
                .highlight_spacing(HighlightSpacing::Always)
                .flex(Flex::Legacy)
                .highlight_symbol(">>>")
                .column_spacing(1);
            let area = Rect::new(0, 0, 10, 3);
            let mut buf = Buffer::empty(area);
            Widget::render(table, area, &mut buf);
            // highlight_symbol and spacing are prioritized but columns are evenly distributed
            #[rustfmt::skip]
            let expected = Buffer::with_lines([
                "   ABC 123",
                "          ",
                "          ",
            ]);
            assert_eq!(buf, expected);

            let table = Table::new(&lines, [Constraint::Fill(1); 2], str_to_row)
                .highlight_spacing(HighlightSpacing::Always)
                .flex(Flex::Start)
                .highlight_symbol(">>>")
                .column_spacing(1);
            let area = Rect::new(0, 0, 10, 3);
            let mut buf = Buffer::empty(area);
            Widget::render(table, area, &mut buf);
            // highlight_symbol and spacing are prioritized but columns are evenly distributed
            #[rustfmt::skip]
            let expected = Buffer::with_lines([
                "   ABC 123",
                "          ",
                "          ",
            ]);
            assert_eq!(buf, expected);

            test_table_with_selection(
                HighlightSpacing::Never,
                10,      // width
                1,       // spacing
                Some(0), // selection
                [
                    "ABCDE 1234", // spacing is prioritized
                    "          ",
                    "          ",
                ],
            );

            test_table_with_selection(
                HighlightSpacing::WhenSelected,
                10,      // width
                1,       // spacing
                Some(0), // selection
                [
                    ">>>ABC 123", // row 1
                    "          ", // row 2
                    "          ", // row 3
                ],
            );

            test_table_with_selection(
                HighlightSpacing::Always,
                10,      // width
                1,       // spacing
                Some(0), // selection
                [
                    ">>>ABC 123", // highlight column and spacing are prioritized
                    "          ", // row 2
                    "          ", // row 3
                ],
            );
        }

        #[test]
        fn insufficient_area_highlight_symbol_allocation_with_no_column_spacing() {
            test_table_with_selection(
                HighlightSpacing::Never,
                10,   // width
                0,    // spacing
                None, // selection
                [
                    "ABCDE12345", // row 1
                    "          ", // row 2
                    "          ", // row 3
                ],
            );
            test_table_with_selection(
                HighlightSpacing::WhenSelected,
                10,   // width
                0,    // spacing
                None, // selection
                [
                    "ABCDE12345", // row 1
                    "          ", // row 2
                    "          ", // row 3
                ],
            );
            // highlight symbol spacing is prioritized over all constraints
            // even if the constraints are fixed length
            // this is because highlight_symbol column is separated _before_ any of the constraint
            // widths are calculated
            test_table_with_selection(
                HighlightSpacing::Always,
                10,   // width
                0,    // spacing
                None, // selection
                [
                    "   ABCD123", // highlight column and spacing are prioritized
                    "          ", // row 2
                    "          ", // row 3
                ],
            );
            test_table_with_selection(
                HighlightSpacing::Never,
                10,      // width
                0,       // spacing
                Some(0), // selection
                [
                    "ABCDE12345", // row 1
                    "          ", // row 2
                    "          ", // row 3
                ],
            );
            test_table_with_selection(
                HighlightSpacing::WhenSelected,
                10,      // width
                0,       // spacing
                Some(0), // selection
                [
                    ">>>ABCD123", // highlight column and spacing are prioritized
                    "          ", // row 2
                    "          ", // row 3
                ],
            );
            test_table_with_selection(
                HighlightSpacing::Always,
                10,      // width
                0,       // spacing
                Some(0), // selection
                [
                    ">>>ABCD123", // highlight column and spacing are prioritized
                    "          ", // row 2
                    "          ", // row 3
                ],
            );
        }
    }

    #[test]
    fn stylize() {
        assert_eq!(
            Table::new(&[[""]], [Constraint::Percentage(100)], str_to_row)
                .black()
                .on_white()
                .bold()
                .not_crossed_out()
                .style,
            Style::new()
                .fg(Color::Black)
                .bg(Color::White)
                .add_modifier(Modifier::BOLD)
                .remove_modifier(Modifier::CROSSED_OUT)
        );
    }
}

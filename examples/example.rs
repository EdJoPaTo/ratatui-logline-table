use std::error::Error;
use std::time::{Duration, Instant, SystemTime};

use ratatui::backend::{Backend, CrosstermBackend};
use ratatui::crossterm::event::{Event, KeyCode, KeyModifiers, MouseEventKind};
use ratatui::layout::{Constraint, Position, Rect};
use ratatui::style::{Color, Modifier, Style};
use ratatui::text::{Line, Span};
use ratatui::widgets::Block;
use ratatui::{Frame, Terminal, crossterm};
use ratatui_logline_table::{State, Table};

enum Update {
    Quit,
    Redraw,
    Skip,
}

struct Logline {
    timestamp: Duration,
    message: String,
}

#[must_use]
struct App {
    start: SystemTime,
    data: Vec<Logline>,
    last_area: Rect,
    render_interval: Duration,
    render_times: Vec<Duration>,
    state: State,
}

impl App {
    const fn new(start: SystemTime) -> Self {
        Self {
            start,
            data: Vec::new(),
            last_area: Rect {
                x: 0,
                y: 0,
                width: 0,
                height: 0,
            },
            render_interval: Duration::from_millis(1000), // 1 FPS
            render_times: Vec::new(),
            state: State::new(),
        }
    }

    fn add_logline<S: Into<String>>(&mut self, message: S) {
        let timestamp = self.start.elapsed().unwrap();
        let message = message.into();
        self.data.push(Logline { timestamp, message });
    }

    #[must_use]
    fn on_event(&mut self, event: &Event) -> Update {
        let change = match event {
            Event::Key(key) => match key.code {
                KeyCode::Char('q') => return Update::Quit,
                KeyCode::Char('c') if key.modifiers.contains(KeyModifiers::CONTROL) => {
                    return Update::Quit;
                }
                KeyCode::Char('+') => {
                    self.render_interval += self.render_interval.min(Duration::from_millis(200));
                    self.add_logline(format!(
                        "Change render interval to {:?}",
                        self.render_interval
                    ));
                    true
                }
                KeyCode::Char('-') => {
                    self.render_interval = self.render_interval.max(Duration::from_millis(50)) / 2;
                    self.add_logline(format!(
                        "Change render interval to {:?}",
                        self.render_interval
                    ));
                    true
                }
                KeyCode::Esc => self.state.select(None),
                KeyCode::Home => self.state.select(Some(0)),
                KeyCode::End => self.state.select(Some(usize::MAX)),
                KeyCode::Down => self.state.select_next(),
                KeyCode::Up => self.state.select_previous(),
                KeyCode::PageDown => self
                    .state
                    .scroll_down_by((self.last_area.height / 2) as usize),
                KeyCode::PageUp => self
                    .state
                    .scroll_up_by((self.last_area.height / 2) as usize),
                KeyCode::Char(char) => {
                    self.add_logline(char.to_string());
                    true
                }
                _ => return Update::Skip,
            },
            Event::Mouse(event) => match event.kind {
                MouseEventKind::ScrollDown => self.state.scroll_down_by(1),
                MouseEventKind::ScrollUp => self.state.scroll_up_by(1),
                MouseEventKind::Down(_) => {
                    self.state.select_at(Position::new(event.column, event.row))
                }
                _ => return Update::Skip,
            },
            Event::Resize(_, _) => return Update::Redraw,
            _ => return Update::Skip,
        };
        if change { Update::Redraw } else { Update::Skip }
    }

    fn draw(&mut self, frame: &mut Frame) {
        let area = frame.area();
        self.last_area = area;
        let widget = Table::new(
            &self.data,
            [
                Constraint::Length(5),
                Constraint::Length(14),
                Constraint::Fill(1),
            ],
            |index, line| {
                [
                    Line::raw(format!("{index:>5}")),
                    Line::raw(format!("{:>14.9}", line.timestamp.as_secs_f32())),
                    Line::raw(&line.message),
                ]
            },
        )
        .header([
            Line::raw("Index"),
            Line::raw("Timestamp"),
            Line::raw("Message"),
        ])
        .header_style(Style::new().add_modifier(Modifier::BOLD))
        .block(
            Block::bordered()
                .title("Logline Table")
                .title_bottom(format!("{} lines", self.data.len())),
        )
        .row_highlight_style(
            Style::new()
                .fg(Color::Black)
                .bg(Color::LightGreen)
                .add_modifier(Modifier::BOLD),
        );
        let instant = Instant::now();
        frame.render_stateful_widget(widget, area, &mut self.state);
        let took = instant.elapsed();
        self.render_times.push(took);

        while self.render_times.len() > 50 {
            self.render_times.remove(0);
        }

        #[allow(clippy::cast_precision_loss)]
        let average_render_time = self
            .render_times
            .iter()
            .sum::<Duration>()
            .div_f64(self.render_times.len() as f64);
        let meta = format!(
            "{} renders, interval: {:?}, avg render time: {average_render_time:?} (last 50 renders)",
            frame.count(),
            self.render_interval
        );
        #[allow(clippy::cast_possible_truncation)]
        let width = meta.len() as u16;
        let meta_area = Rect::new(area.width - width - 1, 0, width, 1);
        frame.render_widget(Span::raw(meta), meta_area);
        self.add_logline(format!("Finished draw successfully: {took:?}"));
    }
}

fn main() -> Result<(), Box<dyn Error>> {
    let start = SystemTime::now();

    // Terminal initialization
    crossterm::terminal::enable_raw_mode()?;
    let mut stdout = std::io::stdout();
    crossterm::execute!(
        stdout,
        crossterm::terminal::EnterAlternateScreen,
        crossterm::event::EnableMouseCapture
    )?;
    let mut terminal = Terminal::new(CrosstermBackend::new(stdout))?;

    // App
    let mut app = App::new(start);
    app.add_logline("Hello world");
    app.add_logline("testing testing");
    app.add_logline("Please ignore this line");
    app.add_logline("Exit with q or CTRL+c");
    app.add_logline("Change the render interval with +/-");

    let res = run_app(&mut terminal, app);

    // restore terminal
    crossterm::terminal::disable_raw_mode()?;
    crossterm::execute!(
        terminal.backend_mut(),
        crossterm::terminal::LeaveAlternateScreen,
        crossterm::event::DisableMouseCapture
    )?;
    terminal.show_cursor()?;

    if let Err(err) = res {
        println!("{err:?}");
    }

    Ok(())
}

fn run_app<B>(terminal: &mut Terminal<B>, mut app: App) -> Result<(), B::Error>
where
    B: Backend,
    B::Error: From<std::io::Error>,
{
    const DEBOUNCE: Duration = Duration::from_millis(20); // 50 FPS
    terminal.draw(|frame| app.draw(frame))?;
    let mut debounce: Option<Instant> = None;
    let mut last_render = Instant::now();
    loop {
        let timeout = debounce.map_or(app.render_interval, |since| {
            DEBOUNCE.saturating_sub(since.elapsed())
        });
        if crossterm::event::poll(timeout)? {
            match app.on_event(&crossterm::event::read()?) {
                Update::Quit => return Ok(()),
                Update::Redraw => {
                    debounce.get_or_insert_with(Instant::now);
                }
                Update::Skip => {}
            }
        }
        if debounce.map_or_else(
            || last_render.elapsed() > app.render_interval,
            |since| since.elapsed() > DEBOUNCE,
        ) {
            terminal.draw(|frame| app.draw(frame))?;
            debounce = None;
            last_render = Instant::now();
        }
    }
}

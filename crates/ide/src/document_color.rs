use hir::Semantics;
use ide_db::{base_db::FileId, RootDatabase};
use syntax::{
    ast::{self, IsString},
    AstNode, AstToken, SyntaxElement, TextRange,
};
use text_edit::TextEdit;

pub struct DocumentColor {
    pub range: TextRange,
    pub color: [f32; 4],
}

pub(crate) fn document_color(db: &RootDatabase, file_id: FileId) -> Option<Vec<DocumentColor>> {
    tracing::info!(?file_id, "");
    let sema = Semantics::new(db);
    let file = sema.parse(file_id);
    let file = file.syntax();

    let mut res = vec![];

    for element in file.descendants_with_tokens() {
        if let SyntaxElement::Token(tok) = element {
            if let Some(string) = ast::String::cast(tok) {
                tracing::info!(%string, "string");
                if let Some(str) = string.value() {
                    if let Some(str) = str.strip_prefix("#") {
                        tracing::info!(%str, "value");
                        if str.chars().all(|it| it.is_ascii_hexdigit()) {
                            let color = match str.len() {
                                3 => {
                                    let col = u16::from_str_radix(str, 16).unwrap();
                                    let r = col & 0xF00;
                                    let g = col & 0x0F0;
                                    let b = col & 0x00F;
                                    let a = 255;
                                    [
                                        r as f32 / 255.0,
                                        g as f32 / 255.0,
                                        b as f32 / 255.0,
                                        a as f32 / 255.0,
                                    ]
                                }
                                4 => {
                                    let col = u16::from_str_radix(str, 16).unwrap();
                                    let r = col & 0xF000;
                                    let g = col & 0x0F00;
                                    let b = col & 0x00F0;
                                    let a = col & 0x000F;
                                    [
                                        r as f32 / 255.0,
                                        g as f32 / 255.0,
                                        b as f32 / 255.0,
                                        a as f32 / 255.0,
                                    ]
                                }
                                6 => {
                                    let col = u32::from_str_radix(str, 16).unwrap();
                                    let r = col & 0xFF0000;
                                    let g = col & 0x00FF00;
                                    let b = col & 0x0000FF;
                                    let a = 255;
                                    [
                                        r as f32 / 255.0,
                                        g as f32 / 255.0,
                                        b as f32 / 255.0,
                                        a as f32 / 255.0,
                                    ]
                                }
                                8 => {
                                    let col = u32::from_str_radix(str, 16).unwrap();
                                    let r = col & 0xFF000000;
                                    let g = col & 0x00FF0000;
                                    let b = col & 0x0000FF00;
                                    let a = col & 0x000000FF;
                                    [
                                        r as f32 / 255.0,
                                        g as f32 / 255.0,
                                        b as f32 / 255.0,
                                        a as f32 / 255.0,
                                    ]
                                }
                                _ => continue,
                            };
                            let range = string.text_range_between_quotes()?;
                            res.push(DocumentColor { range, color });
                        }
                    }
                }
            }
        }
    }

    Some(res)
}
pub struct ColorPresentation {
    pub label: String,
    pub text_edit: Option<TextEdit>,
    pub additional_text_edits: Option<Vec<TextEdit>>,
}

pub(crate) fn color_presentation(
    db: &RootDatabase,
    pos: ide_db::base_db::FileRange,
    color: [f32; 4],
) -> Option<Vec<ColorPresentation>> {
    let sema = Semantics::new(db);
    let file = sema.parse(pos.file_id);
    let file = file.syntax();

    match file.covering_element(pos.range) {
        syntax::NodeOrToken::Node(_) => None,
        syntax::NodeOrToken::Token(tok) => Some(vec![ColorPresentation {
            label: format!(
                "#{:02x}{:02x}{:02x}{:02x}",
                (color[0] * 255.0) as u8,
                (color[1] * 255.0) as u8,
                (color[2] * 255.0) as u8,
                (color[3] * 255.0) as u8
            ),
            text_edit: None,
            additional_text_edits: None,
        }]),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_name() {
        r"
fn main() {
    Rgb::new()
}

struct Rgb;

impl Rgb {
    #[rust_analyzer::color]
    fn new(r: f32, g: f32, b: f32) -> Rgb {
        Rgb
    }
}


";
    }
}
